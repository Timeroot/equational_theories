import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4069`: `x ◇ x = ((x ◇ x) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_x_y_pyx_Equation4069 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4069 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4069.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X2) := by
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
  have eq57 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq60 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) x X2
       have i₂ := eq14 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq71 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ x = (k y x) := by
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
  have eq72 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq68
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq68
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq68 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq108
    | exact resolve eq108 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq375 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 X0 X1
       have i₂ := eq60 X0 X2
       grind)
    | (have i₁ := eq60 X0 X2
       have i₂ := eq60 X0 (M.op X0 X0)
       grind)
    | exact superpose eq60 eq60
    | exact resolve eq60 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq90 X0 X0
       grind)
    | exact superpose eq90 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq90 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq90 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq13 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq90 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq90 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq711 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq710 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq713 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq707 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq719 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq713 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq713 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq713 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq836 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq719 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq719
    | (have j0 := eq719 (τ X0) X1
       grind)
    | exact resolve eq719 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq844 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq836 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq836
    | (have j0 := eq836 X0 X1
       grind)
    | exact resolve eq836 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq850 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq844 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq844
    | (have j0 := eq844 X0 X1
       grind)
    | exact resolve eq844 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq2924 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq711 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq711
    | (have j0 := eq711 (τ X0)
       grind)
    | exact resolve eq711 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq2932 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2924 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2924
    | (have j0 := eq2924 X0
       grind)
    | exact resolve eq2924 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2924
  have eq2938 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2932 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2932
    | (have j0 := eq2932 X0
       grind)
    | exact resolve eq2932 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2932
  have eq8356 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq110 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8357 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq8356
    | exact resolve eq8356 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8356
  have eq8368 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq8357
       have r₂ := eq27
       grind)
    | exact resolve eq8357 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8357
  have eq8370 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq8368
    | exact resolve eq8368 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8368
  have eq8377 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq8370 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq8370
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq8370
       grind)
    | exact resolve eq13 eq8370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8370
  have eq8378 : ∀ X0 : G, x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq8377 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8377
  have eq8384 : ∀ X0 X1 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq8378 X1
       grind)
    | exact superpose eq8378 eq13
    | (have j0 := eq13 X0 x
       have j1 := eq8378 X1
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq8378 X0
       grind)
    | exact resolve eq13 eq8378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8378
  have eq8385 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq8384 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8384
  have eq8519 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq49
       have i₂ := eq8385 (k sF2 sF2) x
       grind)
    | exact superpose eq8385 eq49
    | (have j1 := eq8385 X0 x
       grind)
    | exact resolve eq49 eq8385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8385
  have eq8598 : ∀ X0 : G, x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq8519
    | (have j0 := eq8519 x
       grind)
    | exact resolve eq8519 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8519
  have eq8625 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq8598 X0
       have j1 := eq850 x X0
       grind)
    | (have r₁ := eq8598 X0
       have r₂ := eq850 x x
       grind)
    | (have r₁ := eq8598 x
       have r₂ := eq850 x x
       grind)
    | exact resolve eq8598 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8598
  have eq8667 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2938 x
       have i₂ := eq8625 x
       grind)
    | exact superpose eq8625 eq2938
    | (have j0 := eq2938 x
       grind)
    | (have r₁ := eq2938 x
       have r₂ := eq8625 x
       grind)
    | exact resolve eq2938 eq8625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8625
  have eq8682 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8667
  have eq8752 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq375 x X1 x
       have i₂ := eq8682
       grind)
    | exact superpose eq8682 eq375
    | exact resolve eq375 eq8682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10083 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq8752 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8752
    | (have j0 := eq8752 y X0
       grind)
    | exact resolve eq8752 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8752
  have eq10133 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8682
       have i₂ := eq10083 x
       grind)
    | exact superpose eq10083 eq8682
    | exact resolve eq8682 eq10083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8682 eq10083
  have eq10151 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10133
  have eq10157 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10151 eq72
    | (have r₁ := eq72
       have r₂ := eq10151
       grind)
    | exact resolve eq72 eq10151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq10158 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10151 eq27
    | exact resolve eq27 eq10151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10151
  have eq10159 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq10157
  have eq10177 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10159 eq110
    | exact resolve eq110 eq10159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq10159
  have eq10194 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq10177
  have eq10206 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10194
       have r₂ := eq10158
       grind)
    | exact resolve eq10194 eq10158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10158 eq10194
  have eq10217 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10206 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq10206
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq10206
       grind)
    | exact resolve eq13 eq10206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10206
  have eq10218 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq10217 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10217
  have eq10238 : ∀ X0 X1 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (k X1 (σ x)) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq10218 X1
       grind)
    | exact superpose eq10218 eq13
    | (have j0 := eq13 X0 x
       have j1 := eq10218 X1
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq10218 X0
       grind)
    | exact resolve eq13 eq10218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10218
  have eq10239 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ (k X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq10238 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10238
  have eq10303 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (k X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq49
       have i₂ := eq10239 (k sF2 sF2) x
       grind)
    | exact superpose eq10239 eq49
    | (have j1 := eq10239 X0 x
       grind)
    | exact resolve eq49 eq10239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq10239
  have eq10388 : ∀ X0 : G, x = (k x x) ∨ (k X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28 eq10303
    | (have j0 := eq10303 x
       grind)
    | exact resolve eq10303 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10303
  have eq10416 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq10388 X0
       have j1 := eq850 x X0
       grind)
    | (have r₁ := eq10388 X0
       have r₂ := eq850 x x
       grind)
    | (have r₁ := eq10388 x
       have r₂ := eq850 x x
       grind)
    | exact resolve eq10388 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10388
  have eq10463 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2938 x
       have i₂ := eq10416 x
       grind)
    | exact superpose eq10416 eq2938
    | (have j0 := eq2938 x
       grind)
    | (have r₁ := eq2938 x
       have r₂ := eq10416 x
       grind)
    | exact resolve eq2938 eq10416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2938 eq10416
  have eq10478 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq10463
  have eq10559 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq375 x X1 x
       have i₂ := eq10478
       grind)
    | exact superpose eq10478 eq375
    | exact resolve eq375 eq10478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq12173 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10559 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10559
    | (have j0 := eq10559 y X0
       grind)
    | exact resolve eq10559 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq10559
  have eq12267 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10478
       have i₂ := eq12173 x
       grind)
    | exact superpose eq12173 eq10478
    | exact resolve eq10478 eq12173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10478 eq12173
  have eq12293 : x = (M.op x y) := by grind
  clear eq12267
  have eq12303 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq12293 eq20
    | exact resolve eq20 eq12293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq12308 : x ≠ x ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq12293 eq71
    | (have r₁ := eq71
       have r₂ := eq12293
       grind)
    | exact resolve eq71 eq12293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq12360 : x = (k y x) ∨ x = (M.op x x) := by grind
  clear eq12308
  have eq12415 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq12303
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12303
    | exact resolve eq12303 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12303
  have eq12418 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq12415 eq26
    | exact resolve eq26 eq12415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13415 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq709 x y
       have i₂ := eq12360
       grind)
    | exact superpose eq12360 eq709
    | (have j0 := eq709 x y
       grind)
    | exact resolve eq709 eq12360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709 eq12360
  have eq13418 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq13415
  have eq13421 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13418
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13418
    | exact resolve eq13418 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq13418
  have eq13432 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13421
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13421
    | exact resolve eq13421 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13421
  have eq13442 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq13432
    | exact resolve eq13432 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq13432
  have eq13450 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq12415 eq13442
    | exact resolve eq13442 eq12415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13442
  have eq13451 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq13450
       have r₂ := eq27
       grind)
    | exact resolve eq13450 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13450
  have eq13452 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13451
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13451
    | exact resolve eq13451 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13451
  have eq13453 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq12415 eq13452
    | exact resolve eq13452 eq12415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13452
  have eq13503 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq13453 eq13
    | (have j0 := eq13 X0 (σ (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (σ (M.op x y))
       have r₂ := eq13453
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq13453
       grind)
    | exact resolve eq13 eq13453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13453
  have eq13504 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq13503 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13503
  have eq13523 : ∀ X0 X1 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (k X1 (σ (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq13504 X1
       grind)
    | exact superpose eq13504 eq13
    | (have j0 := eq13 X0 x
       have j1 := eq13504 X1
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq13504 X0
       grind)
    | exact resolve eq13 eq13504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13504
  have eq13524 : ∀ X0 X1 : G, (k X1 (σ (M.op x y))) = X1 ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq13523 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13523
  have eq13565 : ∀ X0 : G, (τ (σ x)) = (k x (M.op x y)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq57
       have i₂ := eq13524 (k sF2 sF1) x
       grind)
    | exact superpose eq13524 eq57
    | (have j1 := eq13524 X0 x
       grind)
    | exact resolve eq57 eq13524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq13524
  have eq13640 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq12293 eq13565
    | (have j0 := eq13565 X0
       grind)
    | exact resolve eq13565 eq12293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12293 eq13565
  have eq13688 : ∀ X0 : G, x = (k x x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq13640
    | (have j0 := eq13640 x
       grind)
    | exact resolve eq13640 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq13640
  have eq13716 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq13688 X0
       have j1 := eq850 x X0
       grind)
    | (have r₁ := eq13688 X0
       have r₂ := eq850 x x
       grind)
    | (have r₁ := eq13688 x
       have r₂ := eq850 x x
       grind)
    | exact resolve eq13688 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850 eq13688
  have eq13782 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq711 x
       have i₂ := eq13716 x
       grind)
    | exact superpose eq13716 eq711
    | (have j0 := eq711 x
       grind)
    | exact resolve eq711 eq13716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq13716
  have eq13806 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq13782
  have eq13822 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq13806
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13806
    | exact resolve eq13806 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq13806
  have eq13874 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq12415 eq13822
    | exact resolve eq13822 eq12415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12415 eq13822
  have eq14190 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq13874 eq60
    | exact resolve eq60 eq13874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq14194 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq13874 eq14190
    | exact resolve eq14190 eq13874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13874 eq14190
  have eq14232 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14194 eq12418
    | exact resolve eq12418 eq14194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12418 eq14194
  have eq14246 : False := by grind
  exact eq14246

/-- `Equation4075`: `x ◇ x = ((x ◇ y) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyx_pyx_pxy_pyx_Equation4075 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4075 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4075.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq103 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq3185 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq103 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq103 X0 X1
       grind)
    | exact superpose eq103 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq103 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq103 X0 X1
       grind)
    | exact resolve eq12 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3186 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq103 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq103 X0 X1
       grind)
    | exact superpose eq103 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq103 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq103 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq103 X0 X1
       grind)
    | exact resolve eq13 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq3225 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3186 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3186
  have eq3246 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3225 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq3225 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq3225 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq3225 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3225
  have eq3247 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3185 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq3185 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq3185 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3185
  have eq3268 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3246 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3246
    | (have j0 := eq3246 X0 X1
       grind)
    | exact resolve eq3246 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3246
  have eq3269 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3268 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3268
  have eq3270 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3247 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3247
    | (have j0 := eq3247 X0 X1
       grind)
    | exact resolve eq3247 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3247
  have eq3271 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3270 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3270
  have eq3280 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3271 X0 X1
       have j1 := eq3269 X0 X1
       grind)
    | (have r₁ := eq3271 X0 X1
       have r₂ := eq3269 X0 X1
       grind)
    | exact resolve eq3271 eq3269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3269 eq3271
  have eq3283 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3280 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3280
    | exact resolve eq3280 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3313 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3280 x y
       grind)
    | exact superpose eq3280 eq16
    | exact resolve eq16 eq3280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3280
  have eq3664 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq3283 X0 (τ X1)
       grind)
    | exact superpose eq3283 eq17
    | exact resolve eq17 eq3283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq3283
  have eq3682 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3664 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3664
    | exact resolve eq3664 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3664
  have eq3692 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3682 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3682
    | exact resolve eq3682 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3682
  have eq3711 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq3313
       have i₂ := eq3692 x y
       grind)
    | exact superpose eq3692 eq3313
    | exact resolve eq3313 eq3692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3313 eq3692
  have eq3712 : False := by grind
  exact eq3712

/-- `Equation4075`: `x ◇ x = ((x ◇ y) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pyx_pyy_pyx_Equation4075 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4075 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4075.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X1) X2) := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
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
  clear eq24
  have eq54 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op x y) y) X0) := by
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
  have eq55 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X2 ∨ (M.op X0 X0) = (k X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 X1) X1)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 (M.op X0 X0) (M.op (M.op X0 X1) X1)
       have r₂ := eq14 X0 X1 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
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
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq73 y x
       grind)
    | exact superpose eq73 eq79
    | (have j1 := eq73 y x
       grind)
    | exact resolve eq79 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94
    | exact resolve eq94 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq100
    | exact resolve eq100 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq120 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X1) X1) ∨ (M.op X0 X0) = X2 ∨ (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (k X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op (M.op X0 X1) X1)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X2 (M.op (M.op X0 X1) X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X2 (M.op (M.op X0 X1) X1)) ∨ (M.op X0 X0) ≠ (M.op (M.op X0 X1) X1) ∨ (M.op X0 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq120 X0 X1 X2
       have i₂ := eq14 X0 X1 (M.op (M.op X0 X1) X1)
       grind)
    | exact superpose eq14 eq120
    | (have j0 := eq120 X0 X1 (k X2 (M.op (M.op X0 X1) X1))
       grind)
    | exact resolve eq120 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq102 eq73
    | (have j0 := eq73 (σ y) (σ x)
       grind)
    | exact resolve eq73 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq126
    | exact resolve eq126 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq130 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq127
       have r₂ := eq27
       grind)
    | exact resolve eq127 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq132 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq130
    | exact resolve eq130 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq234 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq132 eq55
    | exact resolve eq55 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq241 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq234
    | (have j0 := eq234 X0
       grind)
    | exact resolve eq234 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq242 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq132 eq241
    | exact resolve eq241 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq242 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq249 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq247
    | (have j0 := eq247 (σ y)
       grind)
    | exact resolve eq247 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq249 eq247
    | exact resolve eq247 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq262 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq249 eq14
    | exact resolve eq14 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq259 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq409 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ x)) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq132 eq262
    | exact resolve eq262 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq410 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq241 eq262
    | exact resolve eq262 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq262
  have eq416 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq410 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq417 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ x)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq409 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq546 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq263 eq416
    | exact resolve eq416 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq559 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq546 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq635 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq263 eq417
    | exact resolve eq417 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq417
  have eq652 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq635 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq1581 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X1) X1) ∨ (M.op X0 X0) = (k X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq123 X0 X1 X2
       have j1 := eq69 X0 X1 (M.op (M.op X0 X1) X1)
       grind)
    | (have r₁ := eq123 X0 X1 X2
       have r₂ := eq69 X0 X1 (k X2 (M.op (M.op X0 X1) X1))
       grind)
    | (have r₁ := eq123 X0 X1 X2
       have r₂ := eq69 X0 X1 X2
       grind)
    | (have r₁ := eq123 X0 X1 (M.op X0 X0)
       have r₂ := eq69 X0 X1 (M.op X0 X0)
       grind)
    | exact resolve eq123 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq123
  have eq1674 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (k X0 (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq249 eq1581
    | exact resolve eq1581 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq1713 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1674 X0
       grind)
    | (have r₁ := eq1674 X0
       have r₂ := eq559 (σ x)
       grind)
    | exact resolve eq1674 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq1674
  have eq1777 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq652 eq1713
    | exact resolve eq1713 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652 eq1713
  have eq1781 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1777 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1777
  have eq1797 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1781 eq102
    | exact resolve eq102 eq1781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq1781
  have eq1801 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1797
  have eq1807 : x = (M.op x y) := by
    first
    | (have r₁ := eq1801
       have r₂ := eq27
       grind)
    | exact resolve eq1801 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1801
  have eq1810 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1807 eq20
    | exact resolve eq20 eq1807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1812 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq1807 eq54
    | exact resolve eq54 eq1807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1824 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq1812 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1812
    | (have j0 := eq1812 X0
       grind)
    | exact resolve eq1812 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1812
  have eq1826 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1810
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1810
    | exact resolve eq1810 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1810
  have eq1827 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq1807 eq1824
    | exact resolve eq1824 eq1807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1824
  have eq1828 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1826 eq26
    | exact resolve eq26 eq1826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1908 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1827 y
       grind)
    | exact superpose eq1827 eq18
    | (have j1 := eq1827 y
       grind)
    | exact resolve eq18 eq1827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1827
  have eq1924 : x = (M.op x x) := by
    first
    | exact superpose eq1807 eq1908
    | exact resolve eq1908 eq1807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1807 eq1908
  have eq1942 : ∀ X0 : G, x ≠ (M.op x x) ∨ x = (k X0 (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq1581 x x x
       have i₂ := eq1924
       grind)
    | exact superpose eq1924 eq1581
    | exact resolve eq1581 eq1924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1581
  have eq1944 : ∀ X0 : G, x = (k X0 (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq1942 X0
       grind)
    | (have r₁ := eq1942 X0
       have r₂ := eq1924
       grind)
    | exact resolve eq1942 eq1924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1942
  have eq1951 : ∀ X0 : G, x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq1944 X0
       have i₂ := eq1924
       grind)
    | exact superpose eq1924 eq1944
    | exact resolve eq1944 eq1924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1924 eq1944
  have eq2023 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 x
       have i₂ := eq1951 (τ X0)
       grind)
    | exact superpose eq1951 eq34
    | exact resolve eq34 eq1951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1951
  have eq2028 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2023 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2023
    | (have j0 := eq2023 X0
       grind)
    | exact resolve eq2023 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2023
  have eq2032 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1826 eq2028
    | exact resolve eq2028 eq1826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1826 eq2028
  have eq2099 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq2032 eq73
    | (have j0 := eq73 X0 (σ (M.op x y))
       grind)
    | exact resolve eq73 eq2032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq2032
  have eq2101 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have j0 := eq2099 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2099
  have eq2154 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2101 eq1828
    | exact resolve eq1828 eq2101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828 eq2101
  have eq2183 : False := by grind
  exact eq2183

/-- `Equation4075`: `x ◇ x = ((x ◇ y) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyy_pyy_pyx_Equation4075 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4075 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4075.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op b b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X1) X2) := by
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
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X0) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X1) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op x y) y) X0) := by
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
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X1) X1 X2
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq54 X0 x X2 X3
       have i₂ := eq14 X0 x (M.op (M.op X0 x) x)
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq77 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq80 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq82 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq80 (σ X0)
       grind)
    | exact superpose eq80 eq10
    | exact resolve eq10 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq80 x
       grind)
    | exact superpose eq80 eq44
    | exact resolve eq44 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq84 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq80 sF2
       grind)
    | exact superpose eq80 eq50
    | exact resolve eq50 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq85 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq84
       have i₂ := eq80 x
       grind)
    | exact superpose eq80 eq84
    | exact resolve eq84 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq86 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq83
       have i₂ := eq80 sF2
       grind)
    | exact superpose eq80 eq83
    | exact resolve eq83 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq87 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq82
    | exact resolve eq82 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq77
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq77
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq77 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq107
    | exact resolve eq107 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq135 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq138 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq135
       have i₂ := eq80 sF1
       grind)
    | exact superpose eq80 eq135
    | exact resolve eq135 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq140 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq138
       have i₂ := eq80 sF0
       grind)
    | exact superpose eq80 eq138
    | exact resolve eq138 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq138
  have eq232 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 (σ X0) X2 x
       have i₂ := eq87 X0
       grind)
    | exact superpose eq87 eq59
    | exact resolve eq59 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq592 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X2) X4) (M.op (M.op X0 X2) X4)) = (M.op (M.op (M.op X0 X0) X1) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq57 (M.op X0 X2) X4 X3
       have i₂ := eq57 X0 X2 X1
       grind)
    | (have i₁ := eq57 (M.op X0 X0) X1 X2
       have i₂ := eq57 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X1) (M.op x X1)) := by
    intro X1
    first
    | (have i₁ := eq57 x X1 x
       have i₂ := eq232 x
       grind)
    | exact superpose eq232 eq57
    | exact resolve eq57 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq691 : ∀ X0 X2 X4 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X2) X4) (M.op (M.op X0 X2) X4)) := by
    intro X0 X2 X4
    first
    | (have i₁ := eq592 X0 x X2 x X4
       have i₂ := eq59 X0 x x
       grind)
    | exact superpose eq59 eq592
    | exact resolve eq592 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq592
  have eq11375 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq108 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq11376 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq11375
    | exact resolve eq11375 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11375
  have eq11387 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq11376
       have r₂ := eq28
       grind)
    | exact resolve eq11376 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11376
  have eq11541 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq11387 eq85
    | exact resolve eq85 eq11387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11387
  have eq11603 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq11541
    | exact resolve eq11541 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11541
  have eq11604 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11603
  have eq11629 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq232 X0
       have i₂ := eq11604
       grind)
    | exact superpose eq11604 eq232
    | exact resolve eq232 eq11604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq11655 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq691 x x x
       have i₂ := eq11604
       grind)
    | exact superpose eq11604 eq691
    | exact resolve eq691 eq11604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691 eq11604
  have eq11662 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11655 x
       have i₂ := eq604 x
       grind)
    | (have i₁ := eq11655 y
       have i₂ := eq604 x
       grind)
    | exact superpose eq604 eq11655
    | (have j0 := eq11655 y
       grind)
    | exact resolve eq11655 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604 eq11655
  have eq12848 : ∀ X0 : G, x = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq11629 eq11662
    | exact resolve eq11662 eq11629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11629 eq11662
  have eq12896 : ∀ X0 : G, x = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq12848 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12848
  have eq12953 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12896 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12896
    | (have j0 := eq12896 y
       grind)
    | exact resolve eq12896 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12896
  have eq13029 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12953 eq30
    | exact resolve eq30 eq12953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12953
  have eq13134 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq13029
    | exact resolve eq13029 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq13029
  have eq13135 : x = (M.op x y) ∨ x = y := by grind
  clear eq13134
  have eq13150 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq13135 eq21
    | exact resolve eq21 eq13135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13152 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq13135 eq55
    | exact resolve eq55 eq13135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq13166 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq13135 eq140
    | exact resolve eq140 eq13135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq13251 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq13166
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq13166
    | exact resolve eq13166 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13166
  have eq13265 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13152 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13152
    | (have j0 := eq13152 X0
       grind)
    | exact resolve eq13152 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13152
  have eq13267 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq13150
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13150
    | exact resolve eq13150 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13150
  have eq13283 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq13267 eq27
    | exact resolve eq27 eq13267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13267
  have eq14900 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq13135 eq13265
    | exact resolve eq13265 eq13135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13135 eq13265
  have eq14955 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq14900 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14900
  have eq15302 : (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq14955 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14955
    | (have j0 := eq14955 y
       grind)
    | exact resolve eq14955 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14955
  have eq15411 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq86
       have i₂ := eq15302
       grind)
    | exact superpose eq15302 eq86
    | exact resolve eq86 eq15302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq15426 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) X1) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq519 x X1 x
       have i₂ := eq15302
       grind)
    | exact superpose eq15302 eq519
    | exact resolve eq519 eq15302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519 eq15302
  have eq15467 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) X1) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq21 eq15426
    | (have j0 := eq15426 X0 X1
       grind)
    | exact resolve eq15426 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15426
  have eq15477 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq15411
    | exact resolve eq15411 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15411
  have eq15711 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq15477 eq13251
    | exact resolve eq13251 eq15477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13251 eq15477
  have eq15740 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq15711
  have eq21891 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq15740 eq15467
    | exact resolve eq15467 eq15740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15467 eq15740
  have eq21987 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq21891 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21891
  have eq22339 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq21987 eq13283
    | exact resolve eq13283 eq21987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13283 eq21987
  have eq22378 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq22339
  have eq22404 : x = y := by
    first
    | (have r₁ := eq22378
       have r₂ := eq28
       grind)
    | exact resolve eq22378 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22378
  have eq22423 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq22404
       grind)
    | exact superpose eq22404 eq19
    | exact resolve eq19 eq22404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq22424 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq22404
       grind)
    | exact superpose eq22404 eq25
    | exact resolve eq25 eq22404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq22404
  have eq22527 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq22424
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22424
    | exact resolve eq22424 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq22424
  have eq22543 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq22527 eq27
    | exact resolve eq27 eq22527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq22527
  have eq22790 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq22543 eq85
    | exact resolve eq85 eq22543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq22543
  have eq22864 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq22790
       have i₂ := eq22423
       grind)
    | exact superpose eq22423 eq22790
    | exact resolve eq22790 eq22423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22423 eq22790
  have eq22886 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22864 eq15
    | exact resolve eq15 eq22864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22864
  have eq22932 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq22886
    | exact resolve eq22886 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq22886
  have eq22941 : False := by grind
  exact eq22941

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then Y else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_x_y_y_pxx_pxy_Equation4079 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4079 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
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
  have eq179 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 (M.op X0 X1) x x X4
       have i₂ := eq16 X0 X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1045 : (M.op x y) = (k x y) ∨ x = y ∨ x = (M.op x x) := by
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
  have eq1048 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq1062 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1099 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1062 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1045
       grind)
    | exact superpose eq1045 eq40
    | exact resolve eq40 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1045
  have eq1114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1113
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1113
    | exact resolve eq1113 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113
  have eq1116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1114
    | exact resolve eq1114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq1124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq1116 eq1048
    | exact resolve eq1048 eq1116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048 eq1116
  have eq1131 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1124
       have r₂ := eq27
       grind)
    | exact resolve eq1124 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1141 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1131 eq180
    | exact resolve eq180 eq1131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1144 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1131 eq1141
    | exact resolve eq1141 eq1131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131 eq1141
  have eq1164 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1144 eq26
    | (have j1 := eq1144 (σ y)
       grind)
    | exact resolve eq26 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144
  have eq1183 : ∀ X0 : G, x ≠ x ∨ (k x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq1164
       grind)
    | exact superpose eq1164 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq1164
       grind)
    | exact resolve eq13 eq1164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164
  have eq1186 : ∀ X0 : G, (k x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1183 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq1198 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq1186 x
       grind)
    | exact superpose eq1186 eq39
    | exact resolve eq39 eq1186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq1213 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1198
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1198
    | exact resolve eq1198 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq1254 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1213 eq1099
    | (have j0 := eq1099 (σ x)
       grind)
    | (have r₁ := eq1099 (σ x)
       have r₂ := eq1213
       grind)
    | exact resolve eq1099 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213
  have eq1255 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1254
  have eq1366 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1255 eq180
    | exact resolve eq180 eq1255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1369 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1255 eq1366
    | exact resolve eq1366 eq1255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255 eq1366
  have eq1457 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1369 eq26
    | (have j1 := eq1369 (σ y)
       grind)
    | exact resolve eq26 eq1369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq1467 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1457
  have eq1473 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) X0) X1) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq1467 eq179
    | exact resolve eq179 eq1467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq1474 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1467 eq27
    | exact resolve eq27 eq1467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1894 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq26 eq1473
    | (have j0 := eq1473 (σ y) X0
       grind)
    | exact resolve eq1473 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq1950 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1467 eq1894
    | exact resolve eq1894 eq1467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894
  have eq1986 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1950 eq26
    | (have j1 := eq1950 (σ y)
       grind)
    | exact resolve eq26 eq1950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1950
  have eq2013 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1467 eq1986
    | exact resolve eq1986 eq1467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467 eq1986
  have eq2037 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2013 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq2013
       grind)
    | exact resolve eq13 eq2013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2013
  have eq2043 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq2037 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2037
  have eq2079 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2043 eq141
    | exact resolve eq141 eq2043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2043
  have eq2088 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq2079
    | exact resolve eq2079 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2079
  have eq2145 : x ≠ x ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1099 x
       have i₂ := eq2088
       grind)
    | exact superpose eq2088 eq1099
    | (have j0 := eq1099 x
       grind)
    | (have r₁ := eq1099 x
       have r₂ := eq2088
       grind)
    | exact resolve eq1099 eq2088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099 eq2088
  have eq2146 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2145
  have eq2198 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq180 x x x
       have i₂ := eq2146
       grind)
    | exact superpose eq2146 eq180
    | exact resolve eq180 eq2146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq2201 : ∀ X0 : G, x = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2146 eq2198
    | exact resolve eq2198 eq2146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2146 eq2198
  have eq2609 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq2201 y
       grind)
    | exact superpose eq2201 eq18
    | (have j1 := eq2201 y
       grind)
    | exact resolve eq18 eq2201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2201
  have eq2638 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2609 eq31
    | exact resolve eq31 eq2609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2609
  have eq2669 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq2638
    | exact resolve eq2638 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2638
  have eq2670 : x = (M.op x y) ∨ x = y := by grind
  clear eq2669
  have eq2672 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq2670
       grind)
    | exact superpose eq2670 eq22
    | exact resolve eq22 eq2670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2670
  have eq2696 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq2672
    | exact resolve eq2672 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2672
  have eq2722 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2696 eq1474
    | (have r₁ := eq1474
       have r₂ := eq2696
       grind)
    | exact resolve eq1474 eq2696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474 eq2696
  have eq2723 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2722
  have eq2724 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2723
  have eq2909 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2724 eq31
    | exact resolve eq31 eq2724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2724
  have eq2941 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq2909
    | exact resolve eq2909 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2909
  have eq2942 : x = y := by grind
  clear eq2941
  have eq2958 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2942
       grind)
    | exact superpose eq2942 eq18
    | exact resolve eq18 eq2942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2959 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2942
       grind)
    | exact superpose eq2942 eq24
    | exact resolve eq24 eq2942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2942
  have eq2964 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2959
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2959
    | exact resolve eq2959 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2959
  have eq2965 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2964 eq26
    | exact resolve eq26 eq2964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2964
  have eq3010 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq2958
       grind)
    | exact superpose eq2958 eq13
    | (have j0 := eq13 x X0
       grind)
    | exact resolve eq13 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3013 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1062 x
       have i₂ := eq2958
       grind)
    | exact superpose eq2958 eq1062
    | exact resolve eq1062 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2958
  have eq3046 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq2965 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | exact resolve eq13 eq2965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3049 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2965 eq1062
    | exact resolve eq1062 eq2965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062 eq2965
  have eq3492 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq3013
       grind)
    | exact superpose eq3013 eq39
    | exact resolve eq39 eq3013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq3013
  have eq3501 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3492
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3492
    | exact resolve eq3492 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3492
  have eq3503 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq3501
    | exact resolve eq3501 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3501
  have eq3532 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3503 eq3049
    | exact resolve eq3049 eq3503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3545 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3532
       have r₂ := eq27
       grind)
    | exact resolve eq3532 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3532
  have eq3549 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3545 eq27
    | exact resolve eq27 eq3545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3551 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3545 eq3046
    | (have j0 := eq3046 X0
       grind)
    | (have r₁ := eq3046 X0
       have r₂ := eq3545
       grind)
    | exact resolve eq3046 eq3545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3046 eq3545
  have eq3555 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3551 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3551
  have eq3577 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3555 eq3503
    | exact resolve eq3503 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3503
  have eq3591 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3555 eq141
    | exact resolve eq141 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq3555
  have eq3596 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq3577
  have eq3600 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq3591
    | exact resolve eq3591 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3591
  have eq3609 : x = (M.op x y) := by
    first
    | (have r₁ := eq3596
       have r₂ := eq3549
       grind)
    | exact resolve eq3596 eq3549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3549 eq3596
  have eq3623 : x = (k x x) := by
    first
    | (have j1 := eq3010 x
       grind)
    | (have r₁ := eq3600
       have r₂ := eq3010 x
       grind)
    | exact resolve eq3600 eq3010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3010 eq3600
  have eq3631 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq3623
       have i₂ := eq3609
       grind)
    | exact superpose eq3609 eq3623
    | exact resolve eq3623 eq3609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3623
  have eq3637 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq3609
       grind)
    | exact superpose eq3609 eq22
    | exact resolve eq22 eq3609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3609
  have eq3667 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3637 eq20
    | exact resolve eq20 eq3637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3637
  have eq4314 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3631 eq37
    | exact resolve eq37 eq3631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq3631
  have eq4321 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq4314
    | exact resolve eq4314 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4314
  have eq4323 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq3667 eq4321
    | exact resolve eq4321 eq3667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4321
  have eq4401 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4323 eq3049
    | exact resolve eq3049 eq4323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3049 eq4323
  have eq4409 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4401
  have eq4418 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq4409 eq27
    | exact resolve eq27 eq4409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4409
  have eq4427 : False := by grind
  exact eq4427

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_y_pyx_Equation4079 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4079 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq174 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq181 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 (M.op X0 X1) x x X4
       have i₂ := eq16 X0 X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq37 (M.op sF0 sF0)
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq37
    | exact resolve eq37 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq192 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq191
    | exact resolve eq191 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq202 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) X2) := by
    intro X2
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X2) := by
    intro X2
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq90 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq90
    | exact resolve eq90 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq241 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq29 eq230
    | exact resolve eq230 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq248 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq107 (M.op sF3 sF3)
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq107
    | exact resolve eq107 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq259 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq31 eq248
    | exact resolve eq248 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq248
  have eq790 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq797 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq798 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq800 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 X2 X3
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq804 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op (k X0 X1) X2) X3) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 X0 X2 X3
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq833 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq852 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq800 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq1027 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X0 x X2
       have i₂ := eq181 X0 x X1
       grind)
    | (have i₁ := eq181 X0 X0 x
       have i₂ := eq181 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq181 eq181
    | exact resolve eq181 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1036 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq202 x
       have i₂ := eq181 x X0 x
       grind)
    | (have i₁ := eq202 (M.op x x)
       have i₂ := eq181 x x x
       grind)
    | exact superpose eq181 eq202
    | exact resolve eq202 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq1225 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq797
       grind)
    | exact superpose eq797 eq39
    | exact resolve eq39 eq797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1226 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1225
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1225
    | exact resolve eq1225 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1228 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1226
    | exact resolve eq1226 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226
  have eq1236 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1228 eq798
    | exact resolve eq798 eq1228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq1243 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1236
       have r₂ := eq27
       grind)
    | exact resolve eq1236 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236
  have eq1247 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1243
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq1243
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq1243 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1248 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1243 eq259
    | exact resolve eq259 eq1243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq1249 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq1243 eq1027
    | exact resolve eq1027 eq1243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1254 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1243 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243
  have eq1258 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq1254
  have eq1259 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1247
  have eq1261 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq1248
    | exact resolve eq1248 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248
  have eq1262 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1258 eq1259
    | exact resolve eq1259 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258 eq1259
  have eq1263 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq1261
       have r₂ := eq13 y x
       grind)
    | exact resolve eq1261 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261
  have eq1265 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq797
       have i₂ := eq1263
       grind)
    | exact superpose eq1263 eq797
    | exact resolve eq797 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1267 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1263
       grind)
    | exact superpose eq1263 eq39
    | exact resolve eq39 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263
  have eq1268 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1265
  have eq1270 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1267
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1267
    | exact resolve eq1267 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267
  have eq1276 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1270 eq798
    | exact resolve eq798 eq1270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq1280 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1276
  have eq1524 : x = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1268
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq1268
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq1268 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1526 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1027 y X1 x
       have i₂ := eq1268
       grind)
    | exact superpose eq1268 eq1027
    | exact resolve eq1027 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1530 : x = (k y y) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq1268
       grind)
    | exact superpose eq1268 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1535 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq181 y y x
       have i₂ := eq1268
       grind)
    | exact superpose eq1268 eq181
    | exact resolve eq181 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268
  have eq1538 : x = (k y y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1530
  have eq1539 : x = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1524
  have eq1543 : x = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1538 eq1539
    | exact resolve eq1539 eq1538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538 eq1539
  have eq1548 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1280 eq1027
    | exact resolve eq1027 eq1280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1557 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1280 eq181
    | exact resolve eq181 eq1280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280
  have eq1632 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq1526 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq1526 X0 y
       grind)
    | exact superpose eq1526 eq18
    | (have j1 := eq1526 y X0
       grind)
    | exact resolve eq18 eq1526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526
  have eq1903 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x X0) ∨ x = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11 x x
       have i₂ := eq1535 X0
       grind)
    | (have i₁ := eq11 X0 x
       have i₂ := eq1535 X0
       grind)
    | exact superpose eq1535 eq11
    | (have j0 := eq11 X0 x
       grind)
    | exact resolve eq11 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535
  have eq1930 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1903 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1903
  have eq1945 : ∀ X0 : G, (M.op x y) = (k x x) ∨ x = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1632 eq1930
    | (have j0 := eq1930 y
       grind)
    | exact resolve eq1930 eq1632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1930
  have eq1952 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1632 eq1945
    | (have j0 := eq1945 y
       grind)
    | exact resolve eq1945 eq1632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1945
  have eq1953 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1952
  have eq1957 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq1953
       grind)
    | exact superpose eq1953 eq39
    | exact resolve eq39 eq1953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953
  have eq1960 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1957
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1957
    | exact resolve eq1957 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957
  have eq1962 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1960
    | exact resolve eq1960 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960
  have eq2002 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1548 eq26
    | (have j1 := eq1548 (σ y) X0
       grind)
    | exact resolve eq26 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548
  have eq2230 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1557 eq11
    | (have j0 := eq11 X0 (σ x)
       grind)
    | exact resolve eq11 eq1557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1557
  have eq2257 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2230 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2230
  have eq2272 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2002 eq2257
    | (have j0 := eq2257 (σ y)
       grind)
    | exact resolve eq2257 eq2002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2257
  have eq2614 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1270 eq833
    | (have j0 := eq833 (σ x) (σ y)
       grind)
    | exact resolve eq833 eq1270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270
  have eq2627 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2614
    | exact resolve eq2614 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2614
  have eq2628 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2627
  have eq3675 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x x
       have i₂ := eq852 X0 x x x
       grind)
    | exact superpose eq852 eq16
    | (have j1 := eq852 X0 x x x
       grind)
    | exact resolve eq16 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4118 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1249 eq26
    | (have j1 := eq1249 (σ y) X0
       grind)
    | exact resolve eq26 eq1249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249
  have eq6090 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1543
       grind)
    | exact superpose eq1543 eq40
    | exact resolve eq40 eq1543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1543
  have eq6101 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq6090
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6090
    | exact resolve eq6090 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6090
  have eq6104 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq6101
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6101
    | exact resolve eq6101 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6101
  have eq6107 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1632 eq6104
    | exact resolve eq6104 eq1632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1632 eq6104
  have eq6108 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6107
  have eq6111 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6108 eq115
    | exact resolve eq115 eq6108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6127 : x = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq6111
    | exact resolve eq6111 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6111
  have eq7427 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2272 eq1962
    | (have j1 := eq2272 (σ y)
       grind)
    | exact resolve eq1962 eq2272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2272
  have eq7439 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq7427 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7427
  have eq7445 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq7439 X0
       grind)
    | (have r₁ := eq7439 X0
       have r₂ := eq27
       grind)
    | exact resolve eq7439 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7439
  have eq7479 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7445 eq2002
    | (have j1 := eq7445 (σ y)
       grind)
    | exact resolve eq2002 eq7445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7445
  have eq7511 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq7479
  have eq7546 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7511 eq27
    | exact resolve eq27 eq7511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7547 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ y) X0) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq7511 eq180
    | exact resolve eq180 eq7511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7561 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  have eq7773 : ∀ X2 : G, (k (σ y) (σ y)) = (M.op (M.op (σ x) (σ x)) X2) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X2
    first
    | exact superpose eq7547 eq852
    | (have j0 := eq852 (σ y) x X2 x
       grind)
    | exact resolve eq852 eq7547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852 eq7547
  have eq7823 : (k (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq211 eq7773
    | exact resolve eq7773 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq7773
  have eq7850 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6108 eq7823
    | exact resolve eq7823 eq6108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7823
  have eq7865 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7511 eq7850
    | exact resolve eq7850 eq7511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7850
  have eq9858 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2002 eq3675
    | exact resolve eq3675 eq2002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2002
  have eq10060 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9858
  have eq10712 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7865 eq174
    | exact resolve eq174 eq7865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7865
  have eq10745 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6108 eq10712
    | exact resolve eq10712 eq6108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6108 eq10712
  have eq10754 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10745
       have r₂ := eq2628
       grind)
    | exact resolve eq10745 eq2628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2628 eq10745
  have eq10770 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq10754 eq1027
    | exact resolve eq1027 eq10754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10754
  have eq10859 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10770 X0 sF2
       have i₂ := eq3675 sF2
       grind)
    | exact superpose eq3675 eq10770
    | (have j1 := eq3675 (σ x)
       grind)
    | exact resolve eq10770 eq3675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10919 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10770 eq26
    | (have j1 := eq10770 (σ y) X0
       grind)
    | exact resolve eq26 eq10770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10770
  have eq11081 : ∀ X0 : G, (σ y) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7511 eq10919
    | exact resolve eq10919 eq7511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7511 eq10919
  have eq11089 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq1962 eq10859
    | exact resolve eq10859 eq1962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1962 eq10859
  have eq11097 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11081 eq11089
    | exact resolve eq11089 eq11081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11089
  have eq11101 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11097
       have r₂ := eq7546
       grind)
    | exact resolve eq11097 eq7546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7546 eq11097
  have eq11405 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11101 eq11081
    | exact resolve eq11081 eq11101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11081 eq11101
  have eq11424 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq11405
  have eq11472 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11424
       have r₂ := eq7561
       grind)
    | exact resolve eq11424 eq7561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7561 eq11424
  have eq11489 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) X0) X1) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq11472 eq180
    | exact resolve eq180 eq11472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq11725 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq11489
    | (have j0 := eq11489 (σ y) X0
       grind)
    | exact resolve eq11489 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11489
  have eq11879 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11472 eq11725
    | exact resolve eq11725 eq11472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11725
  have eq12006 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11879 eq26
    | (have j1 := eq11879 (σ y)
       grind)
    | exact resolve eq26 eq11879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11879
  have eq12150 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11472 eq12006
    | exact resolve eq12006 eq11472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12006
  have eq12192 : x = (k x (τ (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12150 eq241
    | exact resolve eq241 eq12150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12150
  have eq12293 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq12192
    | exact resolve eq12192 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12192
  have eq12519 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq833 x x
       have i₂ := eq12293
       grind)
    | exact superpose eq12293 eq833
    | (have j0 := eq833 x x
       grind)
    | (have r₁ := eq833 x x
       have r₂ := eq12293
       grind)
    | exact resolve eq833 eq12293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12293
  have eq12520 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq12519
  have eq12521 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq12520
  have eq12582 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq181 x x x
       have i₂ := eq12521
       grind)
    | exact superpose eq12521 eq181
    | exact resolve eq181 eq12521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12621 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12521 eq12582
    | exact resolve eq12582 eq12521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12521 eq12582
  have eq12649 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq12621 y
       grind)
    | exact superpose eq12621 eq18
    | (have j1 := eq12621 y
       grind)
    | exact resolve eq18 eq12621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12621
  have eq12717 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq12649
  have eq12741 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq12717
       grind)
    | exact superpose eq12717 eq18
    | exact resolve eq18 eq12717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12742 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq12717
       grind)
    | exact superpose eq12717 eq24
    | exact resolve eq24 eq12717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq12749 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq797
       have i₂ := eq12717
       grind)
    | exact superpose eq12717 eq797
    | exact resolve eq797 eq12717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797 eq12717
  have eq12767 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq12749
  have eq12769 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq12767
       have r₂ := eq13 (M.op x y) x
       grind)
    | exact resolve eq12767 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12767
  have eq12772 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq12742
    | exact resolve eq12742 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12742
  have eq12894 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12769 eq39
    | exact resolve eq39 eq12769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12769
  have eq12897 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq12894
    | exact resolve eq12894 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12894
  have eq12899 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12772 eq12897
    | exact resolve eq12897 eq12772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12897
  have eq21050 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1262 eq115
    | exact resolve eq115 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq1262
  have eq21081 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq29 eq21050
    | exact resolve eq21050 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21050
  have eq21087 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq6127 eq21081
    | exact resolve eq21081 eq6127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6127 eq21081
  have eq21090 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq11472 eq21087
    | exact resolve eq21087 eq11472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21087
  have eq21415 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq21090 eq4118
    | exact resolve eq4118 eq21090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4118 eq21090
  have eq21500 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq21415
  have eq21554 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq11472 eq21500
    | exact resolve eq21500 eq11472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11472 eq21500
  have eq21555 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21554
  have eq21604 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq21555 eq804
    | (have j0 := eq804 (M.op x y) (M.op x y) x x
       grind)
    | exact resolve eq804 eq21555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21607 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq21604 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21604
  have eq21615 : ∀ X0 X1 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq3675 eq21607
    | (have j1 := eq3675 (M.op x y)
       grind)
    | exact resolve eq21607 eq3675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21607
  have eq21618 : ∀ X0 X1 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq3675 eq21615
    | (have j0 := eq21615 X0 X1
       have j1 := eq3675 (M.op x y)
       grind)
    | exact resolve eq21615 eq3675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21615
  have eq21621 : ∀ X0 X1 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq21555 eq21618
    | (have j0 := eq21618 X0 X1
       grind)
    | exact resolve eq21618 eq21555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21618
  have eq21622 : ∀ X0 X1 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq21621 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21621
  have eq21724 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1036 x
       have i₂ := eq21622 x (M.op x x)
       grind)
    | exact superpose eq21622 eq1036
    | (have j1 := eq21622 y (M.op x y)
       grind)
    | exact resolve eq1036 eq21622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21622
  have eq21801 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21555 eq21724
    | exact resolve eq21724 eq21555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21555 eq21724
  have eq21802 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21801
  have eq21850 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq21802 eq804
    | (have j0 := eq804 (M.op x y) (M.op x y) x x
       grind)
    | exact resolve eq804 eq21802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq21853 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq21850 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21850
  have eq21861 : ∀ X0 X1 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq3675 eq21853
    | (have j1 := eq3675 (M.op x y)
       grind)
    | exact resolve eq21853 eq3675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21853
  have eq21864 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq21802 eq21861
    | exact resolve eq21861 eq21802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21861
  have eq21964 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1036 x
       have i₂ := eq21864 x (M.op x x)
       grind)
    | exact superpose eq21864 eq1036
    | (have j1 := eq21864 y (M.op x y)
       grind)
    | exact resolve eq1036 eq21864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036 eq21864
  have eq22109 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21964 eq174
    | exact resolve eq174 eq21964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq21964
  have eq22162 : x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21802 eq22109
    | exact resolve eq22109 eq21802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21802 eq22109
  have eq22163 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22162
  have eq22204 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq22163 eq1027
    | exact resolve eq1027 eq22163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027 eq22163
  have eq22303 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq22204 X0 x
       have i₂ := eq3675 x
       grind)
    | exact superpose eq3675 eq22204
    | (have j1 := eq3675 x
       grind)
    | exact resolve eq22204 eq3675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3675
  have eq22410 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12741
       have i₂ := eq22204 sF0 x
       grind)
    | (have i₁ := eq12741
       have i₂ := eq22204 X0 sF0
       grind)
    | exact superpose eq22204 eq12741
    | (have j1 := eq22204 y X0
       grind)
    | exact resolve eq12741 eq22204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22204
  have eq22433 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq22410 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22410
  have eq22556 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq22433 eq22303
    | (have j0 := eq22303 y
       grind)
    | exact resolve eq22303 eq22433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22303
  have eq22565 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22433 eq22556
    | exact resolve eq22556 eq22433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22433 eq22556
  have eq22566 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22565
  have eq22585 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq22566
       grind)
    | exact superpose eq22566 eq39
    | exact resolve eq39 eq22566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq22566
  have eq22607 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22585
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22585
    | exact resolve eq22585 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22585
  have eq22611 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq22607
    | exact resolve eq22607 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22607
  have eq22613 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12772 eq22611
    | exact resolve eq22611 eq12772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22611
  have eq22661 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22613 eq10060
    | exact resolve eq10060 eq22613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10060 eq22613
  have eq22683 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq22661
  have eq22805 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22683 eq27
    | exact resolve eq27 eq22683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22683
  have eq22853 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22805
       have r₂ := eq12772
       grind)
    | exact resolve eq22805 eq12772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22805
  have eq22865 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22853 eq27
    | exact resolve eq27 eq22853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22869 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22853 eq790
    | (have r₁ := eq790
       have r₂ := eq22853
       grind)
    | exact resolve eq790 eq22853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq22871 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq22869
  have eq22875 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12899 eq22871
    | exact resolve eq22871 eq12899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12899 eq22871
  have eq22876 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12772 eq22865
    | exact resolve eq22865 eq12772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12772 eq22865
  have eq22877 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq22876
  have eq22920 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22875 eq181
    | exact resolve eq181 eq22875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22875
  have eq22971 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq22920 X0
       grind)
    | (have r₁ := eq22920 X0
       have r₂ := eq22877
       grind)
    | exact resolve eq22920 eq22877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22877 eq22920
  have eq23229 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22971 eq26
    | (have j1 := eq22971 (σ y)
       grind)
    | exact resolve eq26 eq22971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22971
  have eq23485 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22853 eq23229
    | exact resolve eq23229 eq22853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22853 eq23229
  have eq23543 : x = (k x (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23485 eq241
    | exact resolve eq241 eq23485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq23485
  have eq23710 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq23543
    | exact resolve eq23543 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq23543
  have eq24057 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq833 x x
       have i₂ := eq23710
       grind)
    | exact superpose eq23710 eq833
    | (have j0 := eq833 x x
       grind)
    | (have r₁ := eq833 x x
       have r₂ := eq23710
       grind)
    | exact resolve eq833 eq23710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23710
  have eq24058 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq24057
  have eq24059 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq24058
  have eq24141 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq181 x x x
       have i₂ := eq24059
       grind)
    | exact superpose eq24059 eq181
    | exact resolve eq181 eq24059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24197 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq24059 eq24141
    | exact resolve eq24141 eq24059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24059 eq24141
  have eq24274 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12741
       have i₂ := eq24197 sF0
       grind)
    | exact superpose eq24197 eq12741
    | (have j1 := eq24197 y
       grind)
    | exact resolve eq12741 eq24197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12741 eq24197
  have eq24296 : x = (M.op x y) := by grind
  clear eq24274
  have eq24362 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq24296
       grind)
    | exact superpose eq24296 eq18
    | exact resolve eq18 eq24296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq24363 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq24296
       grind)
    | exact superpose eq24296 eq22
    | exact resolve eq22 eq24296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq24381 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq24363 eq20
    | exact resolve eq20 eq24363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24363
  have eq24551 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq24362 eq179
    | exact resolve eq179 eq24362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq24597 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq24551 X0
       have i₂ := eq24296
       grind)
    | exact superpose eq24296 eq24551
    | exact resolve eq24551 eq24296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24296 eq24551
  have eq24644 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq24597 eq24362
    | exact resolve eq24362 eq24597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24362 eq24597
  have eq24756 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq24644 eq192
    | exact resolve eq192 eq24644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq24644
  have eq24828 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq24756
    | exact resolve eq24756 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq24756
  have eq24841 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq24381 eq24828
    | exact resolve eq24828 eq24381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24828
  have eq25044 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq24841 eq833
    | (have j0 := eq833 (σ x) (σ x)
       grind)
    | (have r₁ := eq833 (σ x) (σ x)
       have r₂ := eq24841
       grind)
    | exact resolve eq833 eq24841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833 eq24841
  have eq25045 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq25044
  have eq25046 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq25045
  have eq25160 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq25046 eq181
    | exact resolve eq181 eq25046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq25181 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq25046 eq25160
    | exact resolve eq25160 eq25046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25046 eq25160
  have eq25234 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25181 eq26
    | (have j1 := eq25181 (σ y)
       grind)
    | exact resolve eq26 eq25181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq25181
  have eq25366 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq25234 eq27
    | exact resolve eq27 eq25234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq25234
  have eq25377 : False := by grind
  exact eq25377

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_x_y_x_pxx_pyx_Equation4079 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4079 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  clear eq35
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
  have eq174 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq181 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 (M.op X0 X1) x x X4
       have i₂ := eq16 X0 X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) X2) := by
    intro X2
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X2) := by
    intro X2
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq90 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq90
    | exact resolve eq90 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq241 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq29 eq230
    | exact resolve eq230 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq248 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq107 (M.op sF3 sF3)
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq107
    | exact resolve eq107 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq259 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq31 eq248
    | exact resolve eq248 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq800 : (M.op x y) = (k y x) ∨ x = y ∨ x = (M.op y y) := by
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
  have eq803 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq807 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq879 : ∀ X0 : G, (M.op x x) = (M.op (k (M.op x y) (M.op x y)) X0) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq179 sF0 x
       have i₂ := eq807 sF0
       grind)
    | exact superpose eq807 eq179
    | (have j1 := eq807 (M.op x y)
       grind)
    | exact resolve eq179 eq807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq888 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq180 sF4 x
       have i₂ := eq807 sF4
       grind)
    | exact superpose eq807 eq180
    | (have j1 := eq807 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq180 eq807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq889 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq807 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1015 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X0 x X2
       have i₂ := eq181 X0 x X1
       grind)
    | (have i₁ := eq181 X0 X0 x
       have i₂ := eq181 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq181 eq181
    | exact resolve eq181 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1206 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq800
       grind)
    | exact superpose eq800 eq39
    | exact resolve eq39 eq800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1207 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1206
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1206
    | exact resolve eq1206 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206
  have eq1209 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1207
    | exact resolve eq1207 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq1217 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq1209 eq803
    | exact resolve eq803 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1224 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1217
       have r₂ := eq27
       grind)
    | exact resolve eq1217 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217
  have eq1229 : y = (k y (τ (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq1224 eq259
    | exact resolve eq259 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259 eq1224
  have eq1240 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq1229
    | exact resolve eq1229 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229
  have eq1241 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq1240
       have r₂ := eq13 y x
       grind)
    | exact resolve eq1240 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240
  have eq1243 : y = (M.op x y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq800
       have i₂ := eq1241
       grind)
    | exact superpose eq1241 eq800
    | exact resolve eq800 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq1245 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1241
       grind)
    | exact superpose eq1241 eq39
    | exact resolve eq39 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq1246 : x = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq1243
  have eq1248 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1245
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1245
    | exact resolve eq1245 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1245
  have eq1253 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1248 eq1209
    | exact resolve eq1209 eq1248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq1254 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1248 eq803
    | exact resolve eq803 eq1248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803 eq1248
  have eq1258 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq1254
  have eq1259 : x = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq1253
  have eq1268 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq1015 y X1 x
       have i₂ := eq1246
       grind)
    | exact superpose eq1246 eq1015
    | exact resolve eq1015 eq1246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1270 : x = (k y y) ∨ x = y ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq807 y
       have i₂ := eq1246
       grind)
    | exact superpose eq1246 eq807
    | exact resolve eq807 eq1246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1275 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y y x x
       have i₂ := eq1246
       grind)
    | exact superpose eq1246 eq16
    | exact resolve eq16 eq1246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246
  have eq1276 : x = (k y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq1270
  have eq1536 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq1258 eq1015
    | exact resolve eq1015 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1538 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1258 eq807
    | exact resolve eq807 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1541 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq1258 eq16
    | exact resolve eq16 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1544 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1258 eq181
    | exact resolve eq181 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258
  have eq1547 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq1538
  have eq1555 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq1015 y X1 x
       have i₂ := eq1259
       grind)
    | exact superpose eq1259 eq1015
    | exact resolve eq1015 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015
  have eq1560 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y y x x
       have i₂ := eq1259
       grind)
    | exact superpose eq1259 eq16
    | exact resolve eq16 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259
  have eq1574 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1276
       grind)
    | exact superpose eq1276 eq40
    | exact resolve eq40 eq1276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1577 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1574
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1574
    | exact resolve eq1574 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1574
  have eq1579 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1577
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1577
    | exact resolve eq1577 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1577
  have eq1582 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1547 eq115
    | exact resolve eq115 eq1547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1547
  have eq1589 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq29 eq1582
    | exact resolve eq1582 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1582
  have eq1689 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1268 X0 x
       have i₂ := eq807 x
       grind)
    | exact superpose eq807 eq1268
    | (have j1 := eq807 x
       grind)
    | exact resolve eq1268 eq807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1710 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq1268 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq1268 X0 y
       grind)
    | exact superpose eq1268 eq18
    | (have j1 := eq1268 y X0
       grind)
    | exact resolve eq18 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1713 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq202 X1
       have i₂ := eq1268 x X0
       grind)
    | (have i₁ := eq202 X1
       have i₂ := eq1268 X0 x
       grind)
    | exact superpose eq1268 eq202
    | exact resolve eq202 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268
  have eq1735 : x = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1275 eq1713
    | (have j1 := eq1275 y (M.op x y)
       grind)
    | exact resolve eq1713 eq1275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275 eq1713
  have eq1739 : (M.op x y) = (k x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1710 eq1689
    | (have j0 := eq1689 y
       grind)
    | exact resolve eq1689 eq1710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1689
  have eq1743 : (M.op x y) = (k x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1710 eq1739
    | exact resolve eq1739 eq1710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1739
  have eq1760 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ x = (k x X0) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq1710 x
       grind)
    | exact superpose eq1710 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq1710 x
       grind)
    | exact resolve eq13 eq1710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1710
  have eq1779 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1735
       have i₂ := eq807 sF0
       grind)
    | exact superpose eq807 eq1735
    | (have j1 := eq807 (M.op x y)
       grind)
    | exact resolve eq1735 eq807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1787 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1735 eq807
    | exact resolve eq807 eq1735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1735
  have eq2013 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1536 X0 sF2
       have i₂ := eq807 sF2
       grind)
    | exact superpose eq807 eq1536
    | (have j1 := eq807 (σ x)
       grind)
    | exact resolve eq1536 eq807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2034 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1536 eq26
    | (have j1 := eq1536 (σ y) X0
       grind)
    | exact resolve eq26 eq1536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2037 : ∀ X0 : G, x = (k x (τ (M.op (σ x) X0))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1536 eq241
    | exact resolve eq241 eq1536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2038 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) X0) X1) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq1536 eq211
    | exact resolve eq211 eq1536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq1536
  have eq2059 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1541 eq2038
    | (have j1 := eq1541 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq2038 eq1541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1541 eq2038
  have eq2063 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2034 eq2013
    | (have j0 := eq2013 (σ y)
       grind)
    | exact resolve eq2013 eq2034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2013
  have eq2080 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2034 eq807
    | exact resolve eq807 eq2034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2034
  have eq2107 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2059 eq174
    | exact resolve eq174 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059
  have eq2688 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1555 X0 x
       have i₂ := eq807 x
       grind)
    | exact superpose eq807 eq1555
    | (have j1 := eq807 x
       grind)
    | exact resolve eq1555 eq807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2717 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq1555 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq1555 X0 y
       grind)
    | exact superpose eq1555 eq18
    | (have j1 := eq1555 y X0
       grind)
    | exact resolve eq18 eq1555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2721 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq202 X1
       have i₂ := eq1555 x X0
       grind)
    | (have i₁ := eq202 X1
       have i₂ := eq1555 X0 x
       grind)
    | exact superpose eq1555 eq202
    | exact resolve eq202 eq1555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq1555
  have eq2773 : x = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1560 eq2721
    | (have j1 := eq1560 y (M.op x y)
       grind)
    | exact resolve eq2721 eq1560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1560 eq2721
  have eq2778 : (M.op x y) = (k x x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2717 eq2688
    | (have j0 := eq2688 y
       grind)
    | exact resolve eq2688 eq2717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2688
  have eq2782 : (M.op x y) = (k x x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2717 eq2778
    | exact resolve eq2778 eq2717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2717 eq2778
  have eq3035 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq2773
       have i₂ := eq807 sF0
       grind)
    | exact superpose eq807 eq2773
    | (have j1 := eq807 (M.op x y)
       grind)
    | exact resolve eq2773 eq807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3045 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2773 eq807
    | exact resolve eq807 eq2773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2773
  have eq3839 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq1743
       grind)
    | exact superpose eq1743 eq39
    | exact resolve eq39 eq1743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3842 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3839
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3839
    | exact resolve eq3839 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3839
  have eq3844 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq3842
    | exact resolve eq3842 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3842
  have eq4423 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq2782
       grind)
    | exact superpose eq2782 eq39
    | exact resolve eq39 eq2782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4426 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4423
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4423
    | exact resolve eq4423 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4423
  have eq4428 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4426
    | exact resolve eq4426 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4426
  have eq6075 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1779 eq174
    | exact resolve eq174 eq1779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779
  have eq6186 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2063 eq3844
    | exact resolve eq3844 eq2063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2063 eq3844
  have eq6195 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6186
  have eq6201 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq6195
       have r₂ := eq27
       grind)
    | exact resolve eq6195 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6195
  have eq6290 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3035 eq174
    | exact resolve eq174 eq3035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3035
  have eq6599 : x ≠ (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq6075
  have eq6603 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq6599
       have r₂ := eq1787
       grind)
    | exact resolve eq6599 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1787 eq6599
  have eq6610 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6603 eq41
    | exact resolve eq41 eq6603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6603
  have eq6614 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq6610
    | exact resolve eq6610 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6610
  have eq6616 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6614
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6614
    | exact resolve eq6614 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6614
  have eq6789 : x ≠ (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq6290
  have eq6794 : x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq6789
       have r₂ := eq3045
       grind)
    | exact resolve eq6789 eq3045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3045 eq6789
  have eq6802 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6794 eq41
    | exact resolve eq41 eq6794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6794
  have eq6807 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq6802
    | exact resolve eq6802 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6802
  have eq6809 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6807
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6807
    | exact resolve eq6807 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6807
  have eq6818 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6809 eq889
    | (have j0 := eq889 (σ (M.op x y))
       grind)
    | exact resolve eq889 eq6809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889 eq6809
  have eq8655 : x = (k x (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq6201 eq2037
    | exact resolve eq2037 eq6201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2037 eq6201
  have eq8683 : x = (k x (τ (σ x))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8655
  have eq8714 : x = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq8683
    | exact resolve eq8683 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8683
  have eq8729 : x = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have j1 := eq1760 x
       grind)
    | (have r₁ := eq8714
       have r₂ := eq1760 y
       grind)
    | (have r₁ := eq8714
       have r₂ := eq1760 x
       grind)
    | exact resolve eq8714 eq1760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8714
  have eq8796 : x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1743
       have i₂ := eq8729
       grind)
    | exact superpose eq8729 eq1743
    | exact resolve eq1743 eq8729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743
  have eq8798 : x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2782
       have i₂ := eq8729
       grind)
    | exact superpose eq8729 eq2782
    | exact resolve eq2782 eq8729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2782
  have eq8804 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq8729
       grind)
    | exact superpose eq8729 eq39
    | exact resolve eq39 eq8729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8729
  have eq8812 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq8798
  have eq8814 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq8796
  have eq8824 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8804
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8804
    | exact resolve eq8804 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8804
  have eq8832 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8814 eq27
    | exact resolve eq27 eq8814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8867 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq8824 eq2080
    | exact resolve eq2080 eq8824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8824
  have eq8883 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq8867
  have eq8897 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ y) X0) X1) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq8883 eq180
    | exact resolve eq180 eq8883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq8883
  have eq13451 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (k (σ y) (σ y)) X0) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq8897 sF3 x
       have i₂ := eq807 sF3
       grind)
    | exact superpose eq807 eq8897
    | (have j1 := eq807 (σ y)
       grind)
    | exact resolve eq8897 eq807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8897
  have eq13540 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq1579 eq13451
    | exact resolve eq13451 eq1579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13451
  have eq13556 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq1544 eq13540
    | (have j0 := eq13540 X0
       have j1 := eq1544 X0
       grind)
    | exact resolve eq13540 eq1544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544 eq13540
  have eq13557 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq13556 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13556
  have eq14266 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq13557 eq26
    | (have j1 := eq13557 (σ y)
       grind)
    | exact resolve eq26 eq13557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13557
  have eq17430 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (k (σ y) (σ y)) X0) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8812 eq888
    | exact resolve eq888 eq8812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888 eq8812
  have eq17479 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (k (σ y) (σ y)) X0) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq17430 X0
       grind)
    | (have r₁ := eq17430 X0
       have r₂ := eq8832
       grind)
    | exact resolve eq17430 eq8832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17430
  have eq17493 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (k (σ y) (σ y)) X0) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14266 eq17479
    | exact resolve eq17479 eq14266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14266 eq17479
  have eq17499 : ∀ X0 : G, (σ y) = (M.op (k (σ y) (σ y)) X0) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8814 eq17493
    | exact resolve eq17493 eq8814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8814 eq17493
  have eq17502 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) X0) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1579 eq17499
    | exact resolve eq17499 eq1579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17499
  have eq24902 : ∀ X0 : G, (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) X0) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17502 eq174
    | (have j1 := eq17502 X0
       grind)
    | exact resolve eq174 eq17502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq17502
  have eq24972 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) X0) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1579 eq24902
    | (have j0 := eq24902 X0
       grind)
    | exact resolve eq24902 eq1579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1579 eq24902
  have eq24973 : ∀ X0 : G, (σ y) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq24972 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24972
  have eq25110 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24973 eq807
    | exact resolve eq807 eq24973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24973
  have eq25124 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq25110
  have eq25272 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25124 eq4428
    | exact resolve eq4428 eq25124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4428 eq25124
  have eq25309 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq25272
  have eq25337 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq25309
       have r₂ := eq8832
       grind)
    | exact resolve eq25309 eq8832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8832 eq25309
  have eq25350 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25337 eq31
    | exact resolve eq31 eq25337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25361 : (k y y) = (τ (k (σ x) (σ x))) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25337 eq115
    | exact resolve eq115 eq25337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq25375 : (k x x) = (k y y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq97 eq25361
    | exact resolve eq25361 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq25361
  have eq25386 : x = y ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq25350
    | exact resolve eq25350 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25350
  have eq25387 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq25386
  have eq25403 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1589
       have i₂ := eq25387
       grind)
    | exact superpose eq25387 eq1589
    | exact resolve eq1589 eq25387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1589 eq25387
  have eq25429 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq25403
  have eq26390 : x = (k x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1276
       have i₂ := eq25375
       grind)
    | exact superpose eq25375 eq1276
    | exact resolve eq1276 eq25375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276 eq25375
  have eq26406 : x = (k x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq26390
  have eq26416 : x = (k x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq1760 x
       grind)
    | (have r₁ := eq26406
       have r₂ := eq1760 y
       grind)
    | (have r₁ := eq26406
       have r₂ := eq1760 x
       grind)
    | exact resolve eq26406 eq1760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1760 eq26406
  have eq26422 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq25337 eq26416
    | exact resolve eq26416 eq25337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25337 eq26416
  have eq26438 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26422 eq41
    | exact resolve eq41 eq26422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq26422
  have eq26454 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq26438
    | exact resolve eq26438 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26438
  have eq26458 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq6616 eq26454
    | exact resolve eq26454 eq6616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6616 eq26454
  have eq26465 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26458 eq31
    | exact resolve eq31 eq26458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26508 : x = y ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq26465
    | exact resolve eq26465 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26465
  have eq26509 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq26508
  have eq26561 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26509 eq6818
    | (have r₁ := eq6818
       have r₂ := eq26509
       grind)
    | exact resolve eq6818 eq26509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6818 eq26509
  have eq26599 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq26561
  have eq26600 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq26599
  have eq27361 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26600 eq181
    | exact resolve eq181 eq26600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq27436 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26600 eq27361
    | exact resolve eq27361 eq26600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26600 eq27361
  have eq27683 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq27436 eq26
    | (have j1 := eq27436 (σ y)
       grind)
    | exact resolve eq26 eq27436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27436
  have eq27879 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq27683 eq27
    | exact resolve eq27 eq27683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27683
  have eq28038 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq27879
       have r₂ := eq26458
       grind)
    | exact resolve eq27879 eq26458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26458 eq27879
  have eq28047 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq28038 eq31
    | exact resolve eq31 eq28038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28038
  have eq28090 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq28047
    | exact resolve eq28047 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28047
  have eq28091 : y = (M.op x y) ∨ x = y := by grind
  clear eq28090
  have eq28108 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq28091
       grind)
    | exact superpose eq28091 eq24
    | exact resolve eq24 eq28091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28135 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq28091
  have eq28141 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq28108
    | exact resolve eq28108 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28108
  have eq33473 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq25429 eq879
    | exact resolve eq879 eq25429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879 eq25429
  have eq33500 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq33473 X0
       grind)
    | (have r₁ := eq33473 X0
       have r₂ := eq28135
       grind)
    | exact resolve eq33473 eq28135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33473
  have eq43409 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq33500 y
       grind)
    | exact superpose eq33500 eq18
    | (have j1 := eq33500 y
       grind)
    | exact resolve eq18 eq33500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33500
  have eq43563 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) X1) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq43409 eq16
    | exact resolve eq16 eq43409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43409
  have eq43619 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq179 eq43563
    | exact resolve eq43563 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq43563
  have eq43620 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq43619
  have eq43681 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq807 x
       have i₂ := eq43620
       grind)
    | exact superpose eq43620 eq807
    | exact resolve eq807 eq43620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43620
  have eq43746 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq43681
       have r₂ := eq28135
       grind)
    | exact resolve eq43681 eq28135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28135 eq43681
  have eq43788 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq43746
       grind)
    | exact superpose eq43746 eq39
    | exact resolve eq39 eq43746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43746
  have eq43815 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq43788
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43788
    | exact resolve eq43788 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43788
  have eq43819 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq43815
    | exact resolve eq43815 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43815
  have eq43821 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28141 eq43819
    | exact resolve eq43819 eq28141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43819
  have eq43862 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq43821 eq2080
    | exact resolve eq2080 eq43821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2080
  have eq43921 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq43862
  have eq43957 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq43921 eq27
    | exact resolve eq27 eq43921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43921
  have eq44089 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq43957
       have r₂ := eq28141
       grind)
    | exact resolve eq43957 eq28141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28141 eq43957
  have eq44118 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq44089 eq2107
    | exact resolve eq2107 eq44089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2107
  have eq44271 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq44118
  have eq45034 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq44271 eq43821
    | exact resolve eq43821 eq44271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43821 eq44271
  have eq45042 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq45034
  have eq45087 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq44089 eq45042
    | exact resolve eq45042 eq44089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44089 eq45042
  have eq45088 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq45087
  have eq45097 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq45088 eq31
    | exact resolve eq31 eq45088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq45088
  have eq45178 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq45097
    | exact resolve eq45097 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45097
  have eq45179 : x = y := by grind
  clear eq45178
  have eq45957 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq45179
       grind)
    | exact superpose eq45179 eq18
    | exact resolve eq18 eq45179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq45958 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq45179
       grind)
    | exact superpose eq45179 eq24
    | exact resolve eq24 eq45179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq45179
  have eq45969 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq45958
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45958
    | exact resolve eq45958 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45958
  have eq45970 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq45969 eq26
    | exact resolve eq26 eq45969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq45969
  have eq46069 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq45957
       grind)
    | exact superpose eq45957 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq45957
       grind)
    | exact resolve eq13 eq45957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46074 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq807 x
       have i₂ := eq45957
       grind)
    | exact superpose eq45957 eq807
    | exact resolve eq807 eq45957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45957
  have eq46155 : x = (k x (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq45970 eq241
    | exact resolve eq241 eq45970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq46233 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45970 eq807
    | exact resolve eq807 eq45970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807 eq45970
  have eq48103 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq46074
       grind)
    | exact superpose eq46074 eq39
    | exact resolve eq39 eq46074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48115 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq48103
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq48103
    | exact resolve eq48103 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48103
  have eq48117 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq48115
    | exact resolve eq48115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48115
  have eq48311 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq48117 eq46233
    | exact resolve eq46233 eq48117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48117
  have eq48332 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq48311
       have r₂ := eq27
       grind)
    | exact resolve eq48311 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48311
  have eq48438 : x = (k x (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq48332 eq46155
    | exact resolve eq46155 eq48332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46155 eq48332
  have eq48490 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq48438
    | exact resolve eq48438 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq48438
  have eq48503 : x = (k x x) := by
    first
    | (have j1 := eq46069 x
       grind)
    | (have r₁ := eq48490
       have r₂ := eq46069 x
       grind)
    | exact resolve eq48490 eq46069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46069 eq48490
  have eq48547 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46074
       have i₂ := eq48503
       grind)
    | exact superpose eq48503 eq46074
    | exact resolve eq46074 eq48503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46074
  have eq48549 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq48503
       grind)
    | exact superpose eq48503 eq39
    | exact resolve eq39 eq48503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq48503
  have eq48556 : x = (M.op x y) := by grind
  clear eq48547
  have eq48566 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq48549
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq48549
    | exact resolve eq48549 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48549
  have eq49123 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq48556
       grind)
    | exact superpose eq48556 eq22
    | exact resolve eq22 eq48556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq48556
  have eq49329 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq49123 eq20
    | exact resolve eq20 eq49123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq49123
  have eq49656 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq48566 eq46233
    | exact resolve eq46233 eq48566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46233 eq48566
  have eq49667 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq49656
  have eq49699 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq49667 eq27
    | exact resolve eq27 eq49667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq49667
  have eq49852 : False := by grind
  exact eq49852

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_x_y_pyx_pxy_Equation4079 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4079 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) X3) := by
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
  clear eq24 eq35
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
  have eq57 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X2) X3 X4 X5
       have i₂ := eq14 X0 X1 X2 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0 X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 (M.op X0 X1) x x X4
       have i₂ := eq14 X0 X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X1) X2) ∨ (k (M.op (M.op X0 X1) X2) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op (M.op X0 X1) X2) X3
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X0 X1) X2) X3
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq79
    | exact resolve eq79 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq86
    | exact resolve eq86 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq88
    | exact resolve eq88 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq216 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) X2) := by
    intro X2
    first
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1215 : ∀ X2 : G, (M.op x x) ≠ (M.op (M.op x y) (M.op x y)) ∨ (k (M.op x x) X2) = X2 := by
    intro X2
    first
    | exact superpose eq60 eq66
    | (have j0 := eq66 x y (M.op x y) x
       grind)
    | exact resolve eq66 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1689 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq74 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1691 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1689 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1689
  have eq6063 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1691 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq1691
    | (have j0 := eq1691 (τ X0)
       grind)
    | exact resolve eq1691 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq6071 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6063 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6063
    | (have j0 := eq6063 X0
       grind)
    | exact resolve eq6063 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6063
  have eq6077 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6071 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6071
    | (have j0 := eq6071 X0
       grind)
    | exact resolve eq6071 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6071
  have eq8002 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq89 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq8003 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq8002
    | exact resolve eq8002 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8002
  have eq8014 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq8003
       have r₂ := eq27
       grind)
    | exact resolve eq8003 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8003
  have eq8016 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq8014
    | exact resolve eq8014 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8014
  have eq8020 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq8016 eq13
    | (have j0 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq8016
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq8016
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq8016
       grind)
    | exact resolve eq13 eq8016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8016
  have eq8044 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq8020
  have eq8070 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq8044 eq49
    | exact resolve eq49 eq8044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8044
  have eq8092 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq8070
    | exact resolve eq8070 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8070
  have eq8095 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq6077 x
       grind)
    | (have r₁ := eq8092
       have r₂ := eq6077 x
       grind)
    | exact resolve eq8092 eq6077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6077 eq8092
  have eq8096 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq216 X0
       have i₂ := eq8095
       grind)
    | exact superpose eq8095 eq216
    | exact resolve eq216 eq8095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8098 : x ≠ x ∨ x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq8095
       grind)
    | exact superpose eq8095 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq8095
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq8095
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq8095
       grind)
    | exact resolve eq13 eq8095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8102 : ∀ X0 X1 X2 X3 : G, x = (M.op (M.op (M.op (M.op x X0) X1) X2) X3) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 x x X2 X3 x x
       have i₂ := eq8095
       grind)
    | exact superpose eq8095 eq57
    | exact resolve eq57 eq8095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8095
  have eq8122 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8098
  have eq8133 : ∀ X3 : G, x = (M.op (M.op x x) X3) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X3
    first
    | (have i₁ := eq8102 x x x X3
       have i₂ := eq14 x x x x
       grind)
    | exact superpose eq14 eq8102
    | exact resolve eq8102 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8102
  have eq8141 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8133 x
       have i₂ := eq216 x
       grind)
    | exact superpose eq216 eq8133
    | exact resolve eq8133 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8133
  have eq8147 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq8122
       grind)
    | exact superpose eq8122 eq43
    | exact resolve eq43 eq8122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq8122
  have eq8171 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8147
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8147
    | exact resolve eq8147 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8147
  have eq13325 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq8096 eq8141
    | exact resolve eq8141 eq8096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8096 eq8141
  have eq13380 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq13325 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13325
  have eq13470 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq13380 y
       grind)
    | exact superpose eq13380 eq18
    | (have j1 := eq13380 y
       grind)
    | exact resolve eq18 eq13380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13380
  have eq13506 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13470
  have eq13537 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) X0) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq13506 eq61
    | exact resolve eq61 eq13506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq15065 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq13537
    | (have j0 := eq13537 (σ y) X0
       grind)
    | exact resolve eq13537 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13537
  have eq15219 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13506 eq15065
    | exact resolve eq15065 eq13506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13506 eq15065
  have eq15286 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq15219 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15219
  have eq15335 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq15286
    | (have j0 := eq15286 (σ y)
       grind)
    | exact resolve eq15286 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15286
  have eq15468 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15335 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq15335
       grind)
    | exact resolve eq13 eq15335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15335
  have eq15534 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15468
       have r₂ := eq8171
       grind)
    | exact resolve eq15468 eq8171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8171 eq15468
  have eq15804 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15534 eq49
    | exact resolve eq49 eq15534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq15534
  have eq15826 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq15804
    | exact resolve eq15804 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq15804
  have eq16691 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq15826
       grind)
    | exact superpose eq15826 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq15826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15826
  have eq16692 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq16691
  have eq17189 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq216 X0
       have i₂ := eq16692
       grind)
    | exact superpose eq16692 eq216
    | exact resolve eq216 eq16692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17195 : ∀ X0 X1 X2 X3 : G, x = (M.op (M.op (M.op (M.op x X0) X1) X2) X3) ∨ x = (M.op x y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 x x X2 X3 x x
       have i₂ := eq16692
       grind)
    | exact superpose eq16692 eq57
    | exact resolve eq57 eq16692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq16692
  have eq17230 : ∀ X3 : G, x = (M.op (M.op x x) X3) ∨ x = (M.op x y) := by
    intro X3
    first
    | (have i₁ := eq17195 x x x X3
       have i₂ := eq14 x x x x
       grind)
    | exact superpose eq14 eq17195
    | exact resolve eq17195 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17195
  have eq17238 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17230 x
       have i₂ := eq216 x
       grind)
    | exact superpose eq216 eq17230
    | exact resolve eq17230 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq17230
  have eq27537 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17189 eq17238
    | exact resolve eq17238 eq17189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17189 eq17238
  have eq27613 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq27537 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27537
  have eq28201 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq27613 y
       grind)
    | exact superpose eq27613 eq18
    | (have j1 := eq27613 y
       grind)
    | exact resolve eq18 eq27613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27613
  have eq28254 : x = (M.op x y) := by grind
  clear eq28201
  have eq28301 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq28254 eq20
    | exact resolve eq20 eq28254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq28304 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq28254 eq60
    | exact resolve eq60 eq28254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq28355 : ∀ X0 : G, (M.op x x) ≠ (M.op x x) ∨ (k (M.op x x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq28254 eq1215
    | (have j0 := eq1215 X0
       grind)
    | exact resolve eq1215 eq28254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq28359 : ∀ X0 : G, (k (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28355 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28355
  have eq28411 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq28301
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28301
    | exact resolve eq28301 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28301
  have eq28426 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq28411 eq26
    | exact resolve eq26 eq28411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq36485 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq28304 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28304
    | (have j0 := eq28304 y X0
       grind)
    | exact resolve eq28304 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28304
  have eq36670 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq28254 eq36485
    | exact resolve eq36485 eq28254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36485
  have eq36817 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq36670 y
       grind)
    | exact superpose eq36670 eq18
    | (have j1 := eq36670 y
       grind)
    | exact resolve eq18 eq36670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq36670
  have eq36861 : x = (M.op x x) := by
    first
    | exact superpose eq28254 eq36817
    | exact resolve eq36817 eq28254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28254 eq36817
  have eq36923 : ∀ X0 : G, (k x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq28359 X0
       have i₂ := eq36861
       grind)
    | exact superpose eq36861 eq28359
    | exact resolve eq28359 eq36861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28359 eq36861
  have eq38266 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1691 x
       have i₂ := eq36923 x
       grind)
    | exact superpose eq36923 eq1691
    | (have j0 := eq1691 x
       grind)
    | exact resolve eq1691 eq36923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1691 eq36923
  have eq38343 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq38266
  have eq38398 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq38343
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq38343
    | exact resolve eq38343 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq38343
  have eq38443 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq28411 eq38398
    | exact resolve eq38398 eq28411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28411 eq38398
  have eq41926 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq38443 eq62
    | exact resolve eq62 eq38443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq41979 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq38443 eq41926
    | exact resolve eq41926 eq38443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38443 eq41926
  have eq42790 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41979 eq28426
    | exact resolve eq28426 eq41979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28426 eq41979
  have eq42874 : False := by grind
  exact eq42874
