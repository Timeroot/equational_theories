import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4661`: `(x ◇ y) ◇ y = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pxx_y_pyx_Equation4661 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4661 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4661.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X1 X2) X2) := by
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
  have eq178 : ∀ X0 : G, (M.op (M.op X0 x) x) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq178 X1
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq205 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X1) X1) := by
    intro X1
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq209 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq205 x
       have i₂ := eq193 sF2 x
       grind)
    | exact superpose eq193 eq205
    | (have j1 := eq193 (σ x) (σ y)
       grind)
    | exact resolve eq205 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq219 : ∀ X0 : G, (M.op (M.op (σ y) X0) X0) = (M.op (M.op (M.op x y) y) (σ y)) := by
    intro X0
    first
    | exact superpose eq209 eq16
    | exact resolve eq16 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) (σ y)) := by
    first
    | (have i₁ := eq219 x
       have i₂ := eq193 sF3 x
       grind)
    | exact superpose eq193 eq219
    | exact resolve eq219 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq226 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X1) := by
    intro X1
    first
    | (have i₁ := eq193 (M.op x X1) X1
       have i₂ := eq193 x X1
       grind)
    | (have i₁ := eq193 (M.op x y) y
       have i₂ := eq193 x X1
       grind)
    | exact superpose eq193 eq193
    | exact resolve eq193 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382 : (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq220 eq13
    | (have j0 := eq13 (σ y) (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq13 (σ y) (M.op (M.op x y) y)
       have r₂ := eq220
       grind)
    | exact resolve eq13 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq384 : (M.op (σ y) (σ y)) = (k (σ y) (M.op (M.op x y) y)) := by grind
  clear eq382
  have eq390 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (M.op X0 X0) = (k X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq226 eq13
    | (have j0 := eq13 X0 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq13 x (M.op (M.op x y) y)
       have r₂ := eq226 x
       grind)
    | exact resolve eq13 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have j0 := eq390 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq403 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) ≠ X0 ∨ (k X0 (M.op (M.op x y) y)) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq395 X0
       grind)
    | exact superpose eq395 eq13
    | exact resolve eq13 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq226 (M.op sF0 y)
       have i₂ := eq395 (M.op sF0 y)
       grind)
    | exact superpose eq395 eq226
    | exact resolve eq226 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq682 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) ∨ (k X0 (M.op (M.op x y) y)) = X0 ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq395 X0
       grind)
    | exact superpose eq395 eq11
    | exact resolve eq11 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690 : (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
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
  have eq691 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq732 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have j0 := eq682 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq756 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq732 X0
       have j1 := eq403 X0
       grind)
    | (have r₁ := eq732 X0
       have r₂ := eq403 X0
       grind)
    | exact resolve eq732 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403 eq732
  have eq784 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq395 (M.op sF0 y)
       have i₂ := eq756 (M.op sF0 y)
       grind)
    | exact superpose eq756 eq395
    | exact resolve eq395 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq756 eq384
    | exact resolve eq384 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq799 : ∀ X0 : G, (τ (k (σ X0) (M.op (M.op x y) y))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq506 X0 (σ X0)
       have i₂ := eq756 (σ X0)
       grind)
    | (have i₁ := eq506 X0 (M.op (M.op x y) y)
       have i₂ := eq756 (σ X0)
       grind)
    | exact superpose eq756 eq506
    | exact resolve eq506 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq803 : ∀ X0 : G, (k X0 X0) = (τ (k (σ X0) (M.op (M.op x y) y))) := by
    intro X0
    first
    | (have i₁ := eq799 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq799
    | exact resolve eq799 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq816 : ∀ X0 : G, (k X0 X0) = (k X0 (τ (M.op (M.op x y) y))) := by
    intro X0
    first
    | (have i₁ := eq803 X0
       have i₂ := eq506 X0 (M.op sF0 y)
       grind)
    | exact superpose eq506 eq803
    | exact resolve eq803 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq847 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq193 X0 X0
       have i₂ := eq784 X0
       grind)
    | exact superpose eq784 eq193
    | exact resolve eq193 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq909 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq847 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq847
    | exact resolve eq847 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2832 : (M.op (M.op x y) y) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq406 eq909
    | exact resolve eq909 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2904 : (M.op (M.op x y) y) = (k (σ (M.op (M.op x y) y)) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq2832
       have i₂ := eq395 (σ (M.op sF0 y))
       grind)
    | exact superpose eq395 eq2832
    | exact resolve eq2832 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395 eq2832
  have eq3825 : (τ (M.op (M.op x y) y)) = (k (M.op (M.op x y) y) (τ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq2904 eq506
    | exact resolve eq506 eq2904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506 eq2904
  have eq3829 : (τ (M.op (M.op x y) y)) = (k (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq816 eq3825
    | exact resolve eq3825 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816 eq3825
  have eq3832 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq406 eq3829
    | exact resolve eq3829 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq3829
  have eq3836 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq690
       grind)
    | exact superpose eq690 eq39
    | exact resolve eq39 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq690
  have eq3837 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3836
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3836
    | exact resolve eq3836 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3836
  have eq3839 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq3837
    | exact resolve eq3837 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3837
  have eq3841 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3839
       have i₂ := eq784 y
       grind)
    | exact superpose eq784 eq3839
    | exact resolve eq3839 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784 eq3839
  have eq3865 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq3832 eq14
    | exact resolve eq14 eq3832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3963 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3841 eq691
    | exact resolve eq691 eq3841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691 eq3841
  have eq3970 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3963
       have r₂ := eq27
       grind)
    | exact resolve eq3963 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3963
  have eq3974 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq794 eq3970
    | exact resolve eq3970 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794 eq3970
  have eq4238 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3974 eq115
    | exact resolve eq115 eq3974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq3974
  have eq4254 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq4238
    | exact resolve eq4238 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4238
  have eq4255 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4254
  have eq4267 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq847 y
       have i₂ := eq4255
       grind)
    | exact superpose eq4255 eq847
    | exact resolve eq847 eq4255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq4268 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq909 y
       have i₂ := eq4255
       grind)
    | exact superpose eq4255 eq909
    | exact resolve eq909 eq4255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909 eq4255
  have eq4273 : (M.op (M.op x y) y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4268
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4268
    | exact resolve eq4268 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4268
  have eq4274 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4267
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4267
    | exact resolve eq4267 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4267
  have eq4279 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4273
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4273
    | exact resolve eq4273 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4273
  have eq4283 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq4279
    | exact resolve eq4279 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4279
  have eq4284 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4274 eq4283
    | exact resolve eq4283 eq4274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4283
  have eq4288 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4284 eq209
    | exact resolve eq209 eq4284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4290 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq4292 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq4288
    | exact resolve eq4288 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4288
  have eq4296 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4284 eq4292
    | exact resolve eq4292 eq4284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4284 eq4292
  have eq4390 : (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4274 eq3865
    | exact resolve eq3865 eq4274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4274
  have eq4402 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4390
    | exact resolve eq4390 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4390
  have eq4521 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4402 eq209
    | exact resolve eq209 eq4402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq4523 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq4521
    | exact resolve eq4521 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4521
  have eq4527 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4402 eq4523
    | exact resolve eq4523 eq4402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4523
  have eq4834 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4296 eq226
    | exact resolve eq226 eq4296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4876 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4296 eq3832
    | exact resolve eq3832 eq4296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4296
  have eq4898 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq4876
    | exact resolve eq4876 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4876
  have eq5020 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4898 eq27
    | exact resolve eq27 eq4898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4898
  have eq6463 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4527 eq3832
    | exact resolve eq3832 eq4527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3832 eq4527
  have eq6490 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq6463
    | exact resolve eq6463 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq6463
  have eq6531 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq6490
       have r₂ := eq5020
       grind)
    | exact resolve eq6490 eq5020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5020 eq6490
  have eq6567 : (M.op x y) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6531
       grind)
    | exact superpose eq6531 eq18
    | exact resolve eq18 eq6531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6586 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  clear eq6531
  have eq6644 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6567 eq4834
    | exact resolve eq4834 eq6567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4834 eq6567
  have eq6654 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq6644
  have eq6664 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq6654
       have r₂ := eq4290
       grind)
    | exact resolve eq6654 eq4290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4290 eq6654
  have eq6673 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6664 eq27
    | exact resolve eq27 eq6664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6678 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6664 eq4402
    | exact resolve eq4402 eq6664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4402 eq6664
  have eq6679 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq6678
  have eq6682 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq6679
       have r₂ := eq6586
       grind)
    | exact resolve eq6679 eq6586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6586 eq6679
  have eq6685 : x = (M.op x y) := by
    first
    | (have r₁ := eq6682
       have r₂ := eq6673
       grind)
    | exact resolve eq6682 eq6673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6673 eq6682
  have eq6688 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6685
       grind)
    | exact superpose eq6685 eq18
    | exact resolve eq18 eq6685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq6689 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq6685
       grind)
    | exact superpose eq6685 eq22
    | exact resolve eq22 eq6685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6685
  have eq6846 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq6688 eq226
    | exact resolve eq226 eq6688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq6889 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq6688 eq3865
    | exact resolve eq3865 eq6688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3865 eq6688
  have eq7003 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq6889 eq6689
    | exact resolve eq6689 eq6889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6689
  have eq7004 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq6889 eq20
    | exact resolve eq20 eq6889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq6889
  have eq7049 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq7003 eq26
    | exact resolve eq26 eq7003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq7003
  have eq7102 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6846 eq7049
    | exact resolve eq7049 eq6846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6846 eq7049
  have eq7175 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq7102 eq27
    | exact resolve eq27 eq7102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq7102
  have eq7185 : False := by grind
  exact eq7185

/-- `Equation4670`: `(x ◇ y) ◇ y = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_y_pxx_pyx_Equation4670 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4670 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4670.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq47 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq94 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq94
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq94 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq105
    | exact resolve eq105 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq106
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq106
    | exact resolve eq106 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq216 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq47
    | (have j0 := eq47 (σ x) (σ y)
       grind)
    | exact resolve eq47 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X1) := by
    intro X1
    first
    | (have i₁ := eq47 (M.op x X1) X1
       have i₂ := eq47 x X1
       grind)
    | (have i₁ := eq47 (M.op x y) y
       have i₂ := eq47 x X1
       grind)
    | exact superpose eq47 eq47
    | exact resolve eq47 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq831 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq71 X0 X1
       grind)
    | exact superpose eq71 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq71 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq71 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq71 X1 X1
       grind)
    | exact resolve eq12 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq837 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq831 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq841 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq837 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq837 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq837 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq837 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq852 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq841 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq841
    | (have j0 := eq841 X0 X1
       grind)
    | exact resolve eq841 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq6307 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq852
  have eq6421 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6307 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6307
  have eq6422 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6421 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6421
  have eq6865 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq6422 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq6422
    | (have j0 := eq6422 y
       grind)
    | exact resolve eq6422 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6872 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (σ X0) (σ X0)
       have i₂ := eq6422 X0
       grind)
    | exact superpose eq6422 eq47
    | exact resolve eq47 eq6422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6920 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq6865
       grind)
    | exact superpose eq6865 eq16
    | exact resolve eq16 eq6865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6865
  have eq7941 : (M.op (M.op x y) y) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq217 eq6872
    | exact resolve eq6872 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8073 : (M.op (M.op x y) y) = (σ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y))) := by
    first
    | (have i₁ := eq7941
       have i₂ := eq6422 (M.op sF0 y)
       grind)
    | exact superpose eq6422 eq7941
    | exact resolve eq7941 eq6422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6422 eq7941
  have eq8081 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq217 eq8073
    | exact resolve eq8073 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8073
  have eq8084 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq8081 eq16
    | exact resolve eq16 eq8081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11324 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq107 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq11325 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq11324
    | exact resolve eq11324 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11324
  have eq11338 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq11325
       have r₂ := eq28
       grind)
    | exact resolve eq11325 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11325
  have eq11341 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq11338
    | exact resolve eq11338 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11338
  have eq11343 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq11341 eq6920
    | exact resolve eq6920 eq11341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6920 eq11341
  have eq11355 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq11343
    | exact resolve eq11343 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11343
  have eq11356 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11355
  have eq11363 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6872 y
       have i₂ := eq11356
       grind)
    | exact superpose eq11356 eq6872
    | exact resolve eq6872 eq11356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6872
  have eq11365 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq47 y y
       have i₂ := eq11356
       grind)
    | exact superpose eq11356 eq47
    | exact resolve eq47 eq11356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq11356
  have eq11371 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11365
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11365
    | exact resolve eq11365 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11365
  have eq11372 : (M.op (M.op x y) y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11363
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11363
    | exact resolve eq11363 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq11363
  have eq11376 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11372
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11372
    | exact resolve eq11372 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11372
  have eq11377 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq11376
    | exact resolve eq11376 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11376
  have eq11576 : (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11371 eq8081
    | exact resolve eq8081 eq11371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11585 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq11576
    | exact resolve eq11576 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11576
  have eq11587 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11585 eq216
    | exact resolve eq216 eq11585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11590 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq11587
    | exact resolve eq11587 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11587
  have eq11797 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11377 eq11371
    | exact resolve eq11371 eq11377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11371 eq11377
  have eq11804 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11797
  have eq11810 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11804 eq216
    | exact resolve eq216 eq11804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq11812 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq11814 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq11810
    | exact resolve eq11810 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11810
  have eq12916 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11590 eq217
    | exact resolve eq217 eq11590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12923 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11590 eq8084
    | exact resolve eq8084 eq11590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11590
  have eq13001 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11585 eq12923
    | exact resolve eq12923 eq11585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12923
  have eq13034 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq13001
  have eq13036 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq13034
    | exact resolve eq13034 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13034
  have eq13487 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11814 eq217
    | exact resolve eq217 eq11814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13494 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11814 eq8084
    | exact resolve eq8084 eq11814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8084 eq11814
  have eq13575 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11804 eq13494
    | exact resolve eq13494 eq11804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13494
  have eq13610 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq13575
  have eq13612 : (σ x) = (τ (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq13610
       have r₂ := eq11812
       grind)
    | exact resolve eq13610 eq11812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13610
  have eq13613 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq13612
    | exact resolve eq13612 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq13612
  have eq13616 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq13613 eq28
    | exact resolve eq28 eq13613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13613
  have eq13636 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13616
       have r₂ := eq13036
       grind)
    | exact resolve eq13616 eq13036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13036 eq13616
  have eq14028 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11585 eq12916
    | exact resolve eq12916 eq11585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11585 eq12916
  have eq14040 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq14028 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14028
  have eq14083 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11804 eq13487
    | exact resolve eq13487 eq11804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11804 eq13487
  have eq14097 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq14083 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14083
  have eq14103 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq14097 X0
       grind)
    | (have r₁ := eq14097 X0
       have r₂ := eq11812
       grind)
    | exact resolve eq14097 eq11812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11812 eq14097
  have eq14139 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13636 eq14040
    | exact resolve eq14040 eq13636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14040
  have eq14157 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq14139 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14139
  have eq14225 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13636 eq14103
    | exact resolve eq14103 eq13636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13636 eq14103
  have eq14243 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq14225 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14225
  have eq14848 : x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq14157 y
       grind)
    | exact superpose eq14157 eq19
    | (have j1 := eq14157 y
       grind)
    | exact resolve eq19 eq14157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14157
  have eq14860 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq14848
  have eq15934 : x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19
       have i₂ := eq14243 y
       grind)
    | exact superpose eq14243 eq19
    | (have j1 := eq14243 y
       grind)
    | exact resolve eq19 eq14243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14243
  have eq15946 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15934
  have eq15960 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15946 eq28
    | exact resolve eq28 eq15946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15946
  have eq15984 : x = (M.op x y) := by
    first
    | (have r₁ := eq15960
       have r₂ := eq14860
       grind)
    | exact resolve eq15960 eq14860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14860 eq15960
  have eq15985 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq15984 eq21
    | exact resolve eq21 eq15984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16031 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq15984 eq217
    | exact resolve eq217 eq15984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq16046 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq15984 eq8081
    | exact resolve eq8081 eq15984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8081
  have eq16050 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq16046
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16046
    | exact resolve eq16046 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16046
  have eq16065 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq16031 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16031
    | (have j0 := eq16031 X0
       grind)
    | exact resolve eq16031 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq16031
  have eq16110 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq15985
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15985
    | exact resolve eq15985 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq15985
  have eq16112 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq16050
    | exact resolve eq16050 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq16050
  have eq16119 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq15984 eq16065
    | exact resolve eq16065 eq15984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16065
  have eq16120 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq15984 eq16112
    | exact resolve eq16112 eq15984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15984 eq16112
  have eq16128 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16110 eq27
    | exact resolve eq27 eq16110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq16110
  have eq16780 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq16120 eq16128
    | exact resolve eq16128 eq16120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16128
  have eq16781 : x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16780
       have i₂ := eq16119 sF3
       grind)
    | exact superpose eq16119 eq16780
    | exact resolve eq16780 eq16119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16119 eq16780
  have eq16786 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq16781 eq28
    | exact resolve eq28 eq16781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq16781
  have eq16816 : False := by grind
  exact eq16816

/-- `Equation4670`: `(x ◇ y) ◇ y = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_y_pxx_pyx_Equation4670 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4670 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4670.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 X3) X3) := by
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
  clear eq47
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op (M.op X0 X1) X1) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq16 X2 X3 (M.op x X5) X5
       have i₂ := eq16 x X5 X0 X1
       grind)
    | (have i₁ := eq16 X2 X3 (M.op x X5) X5
       have i₂ := eq16 X0 X1 x X5
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq181
    | (have j0 := eq181 (σ x) (σ y)
       grind)
    | exact resolve eq181 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X1) := by
    intro X1
    first
    | (have i₁ := eq181 (M.op x X1) X1
       have i₂ := eq181 x X1
       grind)
    | (have i₁ := eq181 (M.op x y) y
       have i₂ := eq181 x X1
       grind)
    | exact superpose eq181 eq181
    | exact resolve eq181 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq191 eq174
    | exact resolve eq174 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : (τ (M.op (σ x) (σ x))) = (k x (τ (M.op (σ x) (σ x)))) := by
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
  have eq266 : (τ (M.op (σ y) (σ y))) = (k y (τ (M.op (σ y) (σ y)))) := by
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
  have eq930 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op (k X0 X1) X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq181 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq181
    | (have j1 := eq11 X1 X1
       grind)
    | exact resolve eq181 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq942 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq950 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq955 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq956 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq955 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq1017 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq956 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq956
    | (have j0 := eq956 (σ X0)
       grind)
    | exact resolve eq956 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1999 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq942
       grind)
    | exact superpose eq942 eq39
    | exact resolve eq39 eq942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2000 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1999
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1999
    | exact resolve eq1999 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1999
  have eq2002 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq2000
    | exact resolve eq2000 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2000
  have eq15360 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2002 eq950
    | exact resolve eq950 eq2002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950 eq2002
  have eq15367 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq15360
       have r₂ := eq27
       grind)
    | exact resolve eq15360 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15360
  have eq15439 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15367 eq266
    | exact resolve eq266 eq15367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq15367
  have eq15457 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq15439
    | exact resolve eq15439 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15439
  have eq15464 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq15457
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq15457
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq15457
       have r₂ := eq13 y x
       grind)
    | exact resolve eq15457 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15457
  have eq15470 : (τ (σ x)) = (k x (τ (σ x))) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq15464 eq255
    | exact resolve eq255 eq15464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15464
  have eq15486 : x = (k x x) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq15470
    | exact resolve eq15470 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15470
  have eq15492 : x = (k y x) ∨ x = (k x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq15486
       have r₂ := eq13 x x
       grind)
    | exact resolve eq15486 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15486
  have eq15497 : x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq15492
       have i₂ := eq942
       grind)
    | exact superpose eq942 eq15492
    | exact resolve eq15492 eq942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15500 : x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq942
       have i₂ := eq15492
       grind)
    | exact superpose eq15492 eq942
    | exact resolve eq942 eq15492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq15507 : x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq956 x
       grind)
    | (have r₁ := eq15500
       have r₂ := eq956 x
       grind)
    | exact resolve eq15500 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15500
  have eq15510 : x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq15497
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq15497
       have r₂ := eq13 y x
       grind)
    | exact resolve eq15497 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15497
  have eq15533 : x = (k y y) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq15507
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq15507
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq15507 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15538 : x = (k y y) ∨ x = y ∨ x = y ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq15507
       grind)
    | exact superpose eq15507 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq15507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15541 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq181 y y
       have i₂ := eq15507
       grind)
    | exact superpose eq15507 eq181
    | exact resolve eq181 eq15507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15507
  have eq15544 : x = (k y y) ∨ x = y ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq15538
  have eq15545 : x = (k y y) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq15533
  have eq15548 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15541
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15541
    | exact resolve eq15541 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15541
  have eq15552 : x = (k y y) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq15544 eq15545
    | exact resolve eq15545 eq15544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15544 eq15545
  have eq15553 : x = (k y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq15552
  have eq15567 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1017 x
       have i₂ := eq15510
       grind)
    | exact superpose eq15510 eq1017
    | (have j0 := eq1017 x
       grind)
    | exact resolve eq1017 eq15510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15510
  have eq15576 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq15567
  have eq15577 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq15576
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15576
    | exact resolve eq15576 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15576
  have eq15896 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq15553
       grind)
    | exact superpose eq15553 eq40
    | exact resolve eq40 eq15553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq15553
  have eq15909 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15896
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15896
    | exact resolve eq15896 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15896
  have eq15915 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15909
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15909
    | exact resolve eq15909 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15909
  have eq15960 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15577 eq181
    | exact resolve eq181 eq15577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15962 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (σ x) (σ x)) X2) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0 X1 X2
    first
    | exact superpose eq15577 eq184
    | exact resolve eq184 eq15577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15965 : ∀ X2 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (σ x)) X2) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X2
    first
    | (have i₁ := eq15962 x x X2
       have i₂ := eq182 x x
       grind)
    | (have i₁ := eq15962 (σ x) (σ y) X2
       have i₂ := eq182 x x
       grind)
    | exact superpose eq182 eq15962
    | (have j0 := eq15962 (σ x) (σ y) X2
       grind)
    | exact resolve eq15962 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15962
  have eq15967 : (σ x) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15577 eq15960
    | exact resolve eq15960 eq15577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15960
  have eq15972 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ x)) X2) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X2
    first
    | exact superpose eq190 eq15965
    | exact resolve eq15965 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15965
  have eq15976 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op (σ x) X2) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X2
    first
    | exact superpose eq15577 eq15972
    | exact resolve eq15972 eq15577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15577 eq15972
  have eq15979 : ∀ X2 : G, (σ x) = (M.op (σ x) X2) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X2
    first
    | exact superpose eq15967 eq15976
    | exact resolve eq15976 eq15967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15967 eq15976
  have eq16173 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15915 eq930
    | (have j0 := eq930 (σ y) (σ y)
       grind)
    | exact resolve eq930 eq15915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq16174 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq16173
  have eq16175 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq16174
    | exact resolve eq16174 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16174
  have eq16181 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15548 eq16175
    | exact resolve eq16175 eq15548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15548 eq16175
  have eq16243 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15979 eq26
    | (have j1 := eq15979 (σ y)
       grind)
    | exact resolve eq26 eq15979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16282 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq181 y y
       have i₂ := eq16243
       grind)
    | exact superpose eq16243 eq181
    | exact resolve eq181 eq16243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16284 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) X2) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq184 y y X0 X1 X2
       have i₂ := eq16243
       grind)
    | exact superpose eq16243 eq184
    | exact resolve eq184 eq16243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16243
  have eq16287 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) X2) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16284 X0 X1 X2
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16284
    | (have j0 := eq16284 X0 X1 X2
       grind)
    | exact resolve eq16284 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16284
  have eq16289 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16282
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16282
    | exact resolve eq16282 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16282
  have eq16294 : ∀ X2 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op x y) X2) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | (have i₁ := eq16287 x x X2
       have i₂ := eq182 x x
       grind)
    | (have i₁ := eq16287 (σ x) (σ y) X2
       have i₂ := eq182 x x
       grind)
    | exact superpose eq182 eq16287
    | (have j0 := eq16287 (σ x) (σ y) X2
       grind)
    | exact resolve eq16287 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16287
  have eq16298 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op (M.op x y) X2) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq190 eq16294
    | exact resolve eq16294 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16294
  have eq16301 : ∀ X2 : G, (M.op x y) = (M.op (M.op x y) X2) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq16289 eq16298
    | exact resolve eq16298 eq16289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16298
  have eq16597 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16289 eq245
    | exact resolve eq245 eq16289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16680 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16597 eq1017
    | (have j0 := eq1017 (M.op x y)
       grind)
    | exact resolve eq1017 eq16597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16597
  have eq16686 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16680
  have eq16691 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq16686
    | exact resolve eq16686 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16686
  have eq16732 : (M.op (M.op x y) y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16691 eq181
    | exact resolve eq181 eq16691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16739 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16289 eq16732
    | exact resolve eq16732 eq16289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16289 eq16732
  have eq16754 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16739 eq16691
    | exact resolve eq16691 eq16739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16691 eq16739
  have eq16766 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq16754
  have eq16782 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq16766 eq190
    | exact resolve eq190 eq16766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16784 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq26 eq16782
    | exact resolve eq16782 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16782
  have eq16785 : (σ x) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq16766 eq16784
    | exact resolve eq16784 eq16766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16766 eq16784
  have eq16833 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq16785 eq191
    | exact resolve eq191 eq16785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16875 : (τ (σ x)) = (k x (τ (σ x))) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq16833 eq255
    | exact resolve eq255 eq16833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq16833
  have eq16894 : x = (k x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq29 eq16875
    | exact resolve eq16875 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16875
  have eq16959 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq956 x
       have i₂ := eq16894
       grind)
    | exact superpose eq16894 eq956
    | (have j0 := eq956 x
       grind)
    | (have r₁ := eq956 x
       have r₂ := eq16894
       grind)
    | exact resolve eq956 eq16894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956 eq16894
  have eq16971 : x = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq16959
  have eq16989 : (M.op (M.op x y) y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq181 x x
       have i₂ := eq16971
       grind)
    | exact superpose eq16971 eq181
    | exact resolve eq181 eq16971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16991 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x x) X2) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq184 x x X0 X1 X2
       have i₂ := eq16971
       grind)
    | exact superpose eq16971 eq184
    | exact resolve eq184 eq16971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq16994 : ∀ X2 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op x x) X2) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X2
    first
    | (have i₁ := eq16991 x x X2
       have i₂ := eq182 x x
       grind)
    | (have i₁ := eq16991 (σ x) (σ y) X2
       have i₂ := eq182 x x
       grind)
    | exact superpose eq182 eq16991
    | (have j0 := eq16991 (σ x) (σ y) X2
       grind)
    | exact resolve eq16991 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq16991
  have eq16996 : (σ x) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq16785 eq16989
    | exact resolve eq16989 eq16785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16989
  have eq17000 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op (M.op x x) X2) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X2
    first
    | exact superpose eq190 eq16994
    | exact resolve eq16994 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16994
  have eq17004 : ∀ X2 : G, (σ x) = (M.op (M.op x x) X2) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X2
    first
    | exact superpose eq16785 eq17000
    | exact resolve eq17000 eq16785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16785 eq17000
  have eq17007 : ∀ X2 : G, (σ x) = (M.op x X2) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X2
    first
    | exact superpose eq16971 eq17004
    | exact resolve eq17004 eq16971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17004
  have eq17010 : x = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq16971
       have i₂ := eq16996
       grind)
    | exact superpose eq16996 eq16971
    | exact resolve eq16971 eq16996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16971 eq16996
  have eq17022 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) := by grind
  clear eq17010
  have eq17193 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq17007 y
       grind)
    | (have i₁ := eq18
       have i₂ := eq17007 x
       grind)
    | exact superpose eq17007 eq18
    | (have j1 := eq17007 y
       grind)
    | exact resolve eq18 eq17007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17007
  have eq17228 : x = (τ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq17193 eq29
    | exact resolve eq29 eq17193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17351 : (σ x) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq17022 eq17228
    | exact resolve eq17228 eq17022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17022 eq17228
  have eq17400 : (M.op x y) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq17193 eq17351
    | exact resolve eq17351 eq17193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17193 eq17351
  have eq17459 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq17400 eq14
    | exact resolve eq14 eq17400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17400
  have eq17514 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq17459
    | exact resolve eq17459 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17459
  have eq17515 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq17514
  have eq25463 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16181 eq174
    | exact resolve eq174 eq16181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq16181
  have eq25479 : x = (M.op x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15915 eq25463
    | exact resolve eq25463 eq15915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15915 eq25463
  have eq25508 : (M.op (M.op x y) y) = (M.op x x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq181 x x
       have i₂ := eq25479
       grind)
    | exact superpose eq25479 eq181
    | exact resolve eq181 eq25479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25519 : x = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25479 eq25508
    | exact resolve eq25508 eq25479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25479 eq25508
  have eq25903 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25519 eq16301
    | exact resolve eq16301 eq25519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16301
  have eq25925 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq25903
  have eq25981 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq25925 eq190
    | exact resolve eq190 eq25925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq25985 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq25981
    | exact resolve eq25981 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25981
  have eq25986 : x = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq25519 eq25985
    | exact resolve eq25985 eq25519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25985
  have eq25987 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq25925 eq25986
    | exact resolve eq25986 eq25925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25925 eq25986
  have eq25992 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq25987 eq31
    | exact resolve eq31 eq25987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26131 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq25992
    | exact resolve eq25992 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25992
  have eq26138 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (σ x) := by
    first
    | exact superpose eq26131 eq27
    | exact resolve eq27 eq26131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26131
  have eq26142 : x = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq26138
       have r₂ := eq17515
       grind)
    | exact resolve eq26138 eq17515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26138
  have eq26143 : (M.op x y) = (M.op (σ x) y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq26142
       grind)
    | exact superpose eq26142 eq18
    | exact resolve eq18 eq26142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26198 : (M.op x y) ≠ (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  have eq26474 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26143 eq15979
    | exact resolve eq15979 eq26143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15979
  have eq26486 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = y := by grind
  clear eq26474
  have eq26494 : x = (M.op x y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq26486
       have r₂ := eq26198
       grind)
    | exact resolve eq26486 eq26198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26198 eq26486
  have eq26504 : (σ x) = (M.op y y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26142 eq26494
    | exact resolve eq26494 eq26142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26494
  have eq26530 : (M.op (M.op x y) y) = (M.op (σ x) y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq181 y y
       have i₂ := eq26504
       grind)
    | exact superpose eq26504 eq181
    | exact resolve eq181 eq26504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26504
  have eq26543 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26143 eq26530
    | exact resolve eq26530 eq26143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26143 eq26530
  have eq26586 : x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26543 eq25519
    | exact resolve eq25519 eq26543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25519 eq26543
  have eq26594 : x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq26586
  have eq26602 : (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (σ x) := by
    first
    | exact superpose eq25987 eq26594
    | exact resolve eq26594 eq25987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25987 eq26594
  have eq26807 : y = (τ (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (σ x) := by
    first
    | exact superpose eq26602 eq31
    | exact resolve eq31 eq26602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq26602
  have eq26952 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ y = (σ x) := by
    first
    | exact superpose eq29 eq26807
    | exact resolve eq26807 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq26807
  have eq26959 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ y = (σ x) := by
    first
    | exact superpose eq26952 eq27
    | exact resolve eq27 eq26952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26952
  have eq26967 : y = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq26959
       have r₂ := eq17515
       grind)
    | exact resolve eq26959 eq17515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17515 eq26959
  have eq27052 : x ≠ (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq26967
  have eq27076 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq27052
       have r₂ := eq26142
       grind)
    | exact resolve eq27052 eq26142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26142 eq27052
  have eq27120 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq27076
       grind)
    | exact superpose eq27076 eq18
    | exact resolve eq18 eq27076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27121 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq27076
       grind)
    | exact superpose eq27076 eq22
    | exact resolve eq22 eq27076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27076
  have eq27183 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq27121
    | exact resolve eq27121 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27121
  have eq27323 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27120 eq191
    | exact resolve eq191 eq27120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq27324 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq27120 eq245
    | exact resolve eq245 eq27120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq27426 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq27324 eq1017
    | (have j0 := eq1017 (M.op x y)
       grind)
    | exact resolve eq1017 eq27324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017 eq27324
  have eq27434 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq27426
  have eq27439 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq20 eq27434
    | exact resolve eq27434 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27434
  have eq27446 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq27183 eq27439
    | exact resolve eq27439 eq27183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27439
  have eq27504 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq27446 eq181
    | exact resolve eq181 eq27446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq27511 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq27120 eq27504
    | exact resolve eq27504 eq27120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27120 eq27504
  have eq27547 : (M.op x y) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq27511 eq27446
    | exact resolve eq27446 eq27511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27446 eq27511
  have eq27564 : (M.op x y) = (σ x) ∨ x = y := by grind
  clear eq27547
  have eq27834 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27564 eq26
    | exact resolve eq26 eq27564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28045 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27323 eq27834
    | exact resolve eq27834 eq27323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27323 eq27834
  have eq28265 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq28045 eq27
    | exact resolve eq27 eq28045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28045
  have eq28271 : (M.op x y) ≠ (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq27183 eq28265
    | exact resolve eq28265 eq27183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27183 eq28265
  have eq28278 : (M.op x y) ≠ (σ x) ∨ x = y := by grind
  clear eq28271
  have eq28281 : x = y := by
    first
    | (have r₁ := eq28278
       have r₂ := eq27564
       grind)
    | exact resolve eq28278 eq27564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27564 eq28278
  have eq28284 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28281
       grind)
    | exact superpose eq28281 eq18
    | exact resolve eq18 eq28281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq28285 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq28281
       grind)
    | exact superpose eq28281 eq24
    | exact resolve eq24 eq28281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq28314 : x = (k x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq15492
       have i₂ := eq28281
       grind)
    | exact superpose eq28281 eq15492
    | exact resolve eq15492 eq28281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15492 eq28281
  have eq28359 : x = (k x x) := by grind
  clear eq28314
  have eq28397 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq28285
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28285
    | exact resolve eq28285 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28285
  have eq28403 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq28397 eq26
    | exact resolve eq26 eq28397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq28397
  have eq28564 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq28284
       grind)
    | exact superpose eq28284 eq11
    | exact resolve eq11 eq28284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28284
  have eq28570 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq28564
  have eq28582 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28570
       have i₂ := eq28359
       grind)
    | exact superpose eq28359 eq28570
    | exact resolve eq28570 eq28359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28570
  have eq28583 : x = (M.op x y) := by grind
  clear eq28582
  have eq28588 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq28583
       grind)
    | exact superpose eq28583 eq22
    | exact resolve eq22 eq28583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28583
  have eq28662 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq28588 eq20
    | exact resolve eq20 eq28588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq28588
  have eq29427 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq28359
       grind)
    | exact superpose eq28359 eq39
    | exact resolve eq39 eq28359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq28359
  have eq29452 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq29427
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29427
    | exact resolve eq29427 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq29427
  have eq29501 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28403 eq11
    | exact resolve eq11 eq28403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28403
  have eq29507 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq29501
  have eq29514 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29452 eq29507
    | exact resolve eq29507 eq29452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29452 eq29507
  have eq29515 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq29514
  have eq29533 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq29515 eq27
    | exact resolve eq27 eq29515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq29515
  have eq29539 : False := by grind
  exact eq29539

/-- `Equation575`: `x = y ◇ (z ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_x_pxy_Equation575 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law575 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law575.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 (M.op X1 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X1 X0))) = (M.op X1 (M.op X2 (M.op X2 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X3 (M.op X3 (M.op X1 X0))) X1 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq18
  have eq30 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq30
  have eq45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq72 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq10
    | exact resolve eq10 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X2 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op X2 X0) X2 x X1
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq136 : ∀ X0 X1 X2 X3 : G, (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op X2 (M.op X2 (M.op X3 (σ X1)))) = (M.op X3 (M.op (σ X0) (σ (k X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 (σ X1) X3 (σ X0) X2
       have i₂ := eq126 X0 X1
       grind)
    | exact superpose eq126 eq24
    | (have j1 := eq126 X0 X1
       grind)
    | exact resolve eq24 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq174 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (M.op X1 (M.op X1 (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) (τ X0) X1
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq9
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq315 : ∀ X0 X1 : G, (τ X1) = (M.op X0 (M.op X0 (M.op (τ X1) (τ (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq174 X1 x
       have i₂ := eq24 (τ (M.op X1 X1)) (τ X1) x X0
       grind)
    | (have i₁ := eq174 X0 (τ X0)
       have i₂ := eq24 (τ (M.op X0 X0)) (τ X0) x (τ X0)
       grind)
    | exact superpose eq24 eq174
    | exact resolve eq174 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq174
  have eq367 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 (M.op X1 (M.op (τ (σ X0)) (τ (σ (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq315 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq315
    | exact resolve eq315 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq382 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 (M.op X1 (M.op (τ (σ X0)) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq367 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq367
    | exact resolve eq367 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq384 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X0 X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq382 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq382
    | exact resolve eq382 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq3750 : ∀ X0 X1 X2 X3 : G, (σ X1) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X2 (M.op X2 (M.op X3 X0))) = (M.op X3 (M.op (σ X1) (σ (k X1 (τ X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq136 X0 (τ X0) X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq136
    | exact resolve eq136 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq3893 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (M.op X2 (M.op X2 (M.op X3 X0))) = (M.op X3 (M.op (σ X1) (σ (k X1 (τ X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3750 X0 X1 X2 X3
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq3750
    | (have j0 := eq3750 X0 X1 X2 X3
       grind)
    | exact resolve eq3750 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3750
  have eq3909 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X0 (σ X1)) ∨ (M.op X2 (M.op X2 (M.op X3 X0))) = (M.op X3 (M.op (σ X1) (k (σ X1) X0))) ∨ (σ X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3893 X0 X1 X2 X3
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq3893
    | (have j0 := eq3893 X0 X1 X2 X3
       grind)
    | exact resolve eq3893 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3893
  have eq12936 : ∀ X0 X1 X2 X3 X4 : G, (σ X2) = (M.op X1 (M.op X1 (M.op X0 (M.op X0 X0)))) ∨ (M.op X3 (M.op X3 (M.op X4 X0))) = (M.op X4 (M.op (σ X2) (k (σ X2) X0))) ∨ (σ X2) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq109 (σ X2) X1 X0
       have i₂ := eq3909 X0 X2 X3 X4
       grind)
    | (have i₁ := eq109 X0 X1 X0
       have i₂ := eq3909 X0 X1 X2 X3
       grind)
    | exact superpose eq3909 eq109
    | (have j1 := eq3909 X0 X2 X3 X4
       grind)
    | exact resolve eq109 eq3909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq3909
  have eq13014 : ∀ X0 X2 X3 X4 : G, (σ X2) = X0 ∨ (M.op X3 (M.op X3 (M.op X4 X0))) = (M.op X4 (M.op (σ X2) (k (σ X2) X0))) ∨ (σ X2) = X0 := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq12936 X0 x X2 X3 X4
       have i₂ := eq384 X0 x
       grind)
    | exact superpose eq384 eq12936
    | (have j0 := eq12936 X0 x X2 X3 X4
       grind)
    | exact resolve eq12936 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384 eq12936
  have eq13015 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X3 (M.op X4 X0))) = (M.op X4 (M.op (σ X2) (k (σ X2) X0))) ∨ (σ X2) = X0 := by
    intro X0 X2 X3 X4
    first
    | (have j0 := eq13014 X0 X2 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13014
  have eq52212 : ∀ X0 X1 X2 X3 : G, (k (σ X3) X2) = (M.op (σ X3) (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2))))) ∨ (σ X3) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (k (σ X3) X2) (σ X3) X1
       have i₂ := eq13015 X2 X3 X0 X1
       grind)
    | exact superpose eq13015 eq9
    | (have j1 := eq13015 X2 X3 X3 x
       grind)
    | exact resolve eq9 eq13015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13015
  have eq52409 : ∀ X2 X3 : G, (k (σ X3) X2) = (M.op (σ X3) X2) ∨ (σ X3) = X2 := by
    intro X2 X3
    first
    | (have i₁ := eq52212 x x X2 X3
       have i₂ := eq9 X2 x x
       grind)
    | exact superpose eq9 eq52212
    | (have j0 := eq52212 x x X2 X3
       grind)
    | exact resolve eq52212 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52212
  have eq52647 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52409 x (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq52409
    | exact resolve eq52409 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52694 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52409 (σ X1) X0
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq52409
    | (have j0 := eq52409 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq52409 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52409
  have eq62584 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq52694 x y
       grind)
    | exact superpose eq52694 eq16
    | (have j1 := eq52694 x y
       grind)
    | exact resolve eq16 eq52694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52694
  have eq64056 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq62584
       have i₂ := eq52647 x y
       grind)
    | exact superpose eq52647 eq62584
    | (have j1 := eq52647 (σ x) (σ y)
       grind)
    | (have r₁ := eq62584
       have r₂ := eq52647 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq62584
       have r₂ := eq52647 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq62584 eq52647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52647 eq62584
  have eq64067 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq64056
  have eq65360 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq64067
       grind)
    | exact superpose eq64067 eq16
    | exact resolve eq16 eq64067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64067
  have eq65365 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq65360
       have r₂ := eq22 x
       grind)
    | exact resolve eq65360 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65360
  have eq66745 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq65365
       grind)
    | exact superpose eq65365 eq10
    | exact resolve eq10 eq65365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65365
  have eq66949 : x = y := by
    first
    | (have i₁ := eq66745
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq66745
    | exact resolve eq66745 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66745
  have eq68418 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66949
       grind)
    | exact superpose eq66949 eq16
    | exact resolve eq16 eq66949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66949
  have eq68423 : False := by grind
  exact eq68423

/-- `Equation58`: `x = x ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxy_pxx_pxy_Equation58 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law58 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law58.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq31 (σ X0)
       grind)
    | exact superpose eq31 eq15
    | exact resolve eq15 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq33
    | exact resolve eq33 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq33
  have eq51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq36 X1
       grind)
    | exact superpose eq36 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq76 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq54 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq54
    | exact resolve eq54 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq179 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq158 X0 X1
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq158
    | (have j0 := eq158 X0 X1
       grind)
    | exact resolve eq158 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq184 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq179 X0 X1
       have j1 := eq76 X1 X0
       grind)
    | (have r₁ := eq179 X1 X0
       have r₂ := eq76 X0 X1
       grind)
    | (have r₁ := eq179 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq179 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq179
  have eq236 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq184 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq184
    | exact resolve eq184 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq184 (σ X0) X1
       grind)
    | exact superpose eq184 eq15
    | (have j1 := eq184 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq250 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1
       have i₂ := eq236 X1 (τ X0)
       grind)
    | exact superpose eq236 eq24
    | (have j1 := eq236 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq24 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq236
  have eq511 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq250 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq250
    | exact resolve eq250 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq550 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq511 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq511
    | (have j0 := eq511 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq511 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq1137 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
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
  clear eq241
  have eq1227 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1137
       have i₂ := eq550 x y
       grind)
    | exact superpose eq550 eq1137
    | (have j1 := eq550 (σ x) (σ y)
       grind)
    | (have r₁ := eq1137
       have r₂ := eq550 x y
       grind)
    | (have r₁ := eq1137
       have r₂ := eq550 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1137
       have r₂ := eq550 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1137 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550 eq1137
  have eq1228 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1227
  have eq1232 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1228
       grind)
    | exact superpose eq1228 eq10
    | exact resolve eq10 eq1228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq1277 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1232
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1232
    | exact resolve eq1232 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1232
  have eq1278 : x = y := by grind
  clear eq1277
  have eq1344 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1278
       grind)
    | exact superpose eq1278 eq16
    | exact resolve eq16 eq1278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278
  have eq1345 : False := by grind
  exact eq1345

/-- `Equation58`: `x = x ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then X else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_x_pyy_pxy_Equation58 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law58 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law58.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq43 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq48 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq31
  have eq114 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq43 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq43 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq43 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq43 X0 X1
       grind)
    | exact resolve eq13 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq127 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq128 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq127 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq130 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq128 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq128
    | (have j0 := eq128 X0 X1
       grind)
    | exact resolve eq128 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq133 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq130 X0 X1
       have j1 := eq124 X1 X0
       grind)
    | (have r₁ := eq130 X1 X0
       have r₂ := eq124 X0 X1
       grind)
    | (have r₁ := eq130 X1 (k X0 X1)
       have r₂ := eq124 X0 X1
       grind)
    | (have r₁ := eq130 X1 X1
       have r₂ := eq124 X1 X1
       grind)
    | exact resolve eq130 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq130
  have eq609 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq133 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq133
    | exact resolve eq133 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq616 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq133 y x
       grind)
    | exact superpose eq133 eq16
    | (have j1 := eq133 y x
       grind)
    | exact resolve eq16 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq634 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq609 X0 X1
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq609
    | (have j0 := eq609 X0 X1
       grind)
    | exact resolve eq609 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq609
  have eq736 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq634 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq634
    | exact resolve eq634 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq862 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq736 (τ X0) X1
       grind)
    | exact superpose eq736 eq20
    | (have j1 := eq736 (τ X0) X1
       grind)
    | exact resolve eq20 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1064 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq862 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq862
    | exact resolve eq862 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq1118 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1064 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1064
    | (have j0 := eq1064 X0 X1
       grind)
    | exact resolve eq1064 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq2055 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq616
       have i₂ := eq1118 x y
       grind)
    | exact superpose eq1118 eq616
    | (have j1 := eq1118 (σ x) (σ y)
       grind)
    | (have r₁ := eq616
       have r₂ := eq1118 x y
       grind)
    | exact resolve eq616 eq1118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118
  have eq2056 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2055
  have eq2062 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  have eq2067 : x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq19 y y
       have i₂ := eq2056
       grind)
    | exact superpose eq2056 eq19
    | exact resolve eq19 eq2056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2056
  have eq2174 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq616
       have i₂ := eq2062
       grind)
    | exact superpose eq2062 eq616
    | exact resolve eq616 eq2062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616 eq2062
  have eq2179 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2174
  have eq2321 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2179
       have i₂ := eq2067
       grind)
    | exact superpose eq2067 eq2179
    | exact resolve eq2179 eq2067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2067 eq2179
  have eq2322 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2321
  have eq2323 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2322
  have eq2417 : (τ (σ x)) = (k (τ (σ x)) y) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq2323
       grind)
    | exact superpose eq2323 eq48
    | exact resolve eq48 eq2323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq2428 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19 (σ y) (σ y)
       have i₂ := eq2323
       grind)
    | exact superpose eq2323 eq19
    | exact resolve eq19 eq2323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2323
  have eq2442 : x = (k x y) := by
    first
    | (have i₁ := eq2417
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2417
    | exact resolve eq2417 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2417
  have eq2456 : x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq736 x y
       have i₂ := eq2442
       grind)
    | exact superpose eq2442 eq736
    | (have j0 := eq736 x y
       grind)
    | exact resolve eq736 eq2442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736 eq2442
  have eq2585 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2428
       grind)
    | exact superpose eq2428 eq16
    | exact resolve eq16 eq2428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2428
  have eq2758 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2585
       have i₂ := eq2456
       grind)
    | exact superpose eq2456 eq2585
    | exact resolve eq2585 eq2456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2456
  have eq2771 : x = (M.op y y) := by grind
  clear eq2758
  have eq2828 : x = (M.op x y) := by
    first
    | (have i₁ := eq19 y y
       have i₂ := eq2771
       grind)
    | exact superpose eq2771 eq19
    | exact resolve eq19 eq2771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq2771
  have eq2836 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2585
       have i₂ := eq2828
       grind)
    | exact superpose eq2828 eq2585
    | exact resolve eq2585 eq2828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2585 eq2828
  have eq2849 : False := by grind
  exact eq2849

/-- `Equation626`: `x = x ◇ (x ◇ ((y ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation626 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law626 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law626.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq359 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq6366 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq359 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq359
    | (have j0 := eq359 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq359 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548336 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq6366 x y
       grind)
    | exact superpose eq6366 eq16
    | (have j1 := eq6366 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq6366 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq6366 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq6366 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq6366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6366
  have eq548832 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq548336
  have eq5330878 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq548832
       grind)
    | exact superpose eq548832 eq16
    | exact resolve eq16 eq548832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5330880 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq548832
       grind)
    | exact superpose eq548832 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq548832
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq548832
       grind)
    | exact resolve eq13 eq548832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548832
  have eq5331158 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq5330880
  have eq5331159 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq5331158
  have eq5331162 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5331159
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq5331159
    | exact resolve eq5331159 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5331159
  have eq5331164 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq14 eq5331162
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq5331162 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5331162
  have eq5331166 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq5331164
       have r₂ := eq5330878
       grind)
    | exact resolve eq5331164 eq5330878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5330878 eq5331164
  have eq5331169 : x ≠ x ∨ x = y ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq5331166
       grind)
    | exact superpose eq5331166 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq5331166
       grind)
    | exact resolve eq13 eq5331166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5331447 : x ≠ x ∨ x = y ∨ x = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq5331169
  have eq5331448 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq5331447
  have eq5331450 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq359 y x
       have i₂ := eq5331448
       grind)
    | exact superpose eq5331448 eq359
    | (have j0 := eq359 y x
       grind)
    | exact resolve eq359 eq5331448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359 eq5331448
  have eq5331453 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5331450
  have eq5331456 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq5331453
       grind)
    | exact superpose eq5331453 eq16
    | exact resolve eq16 eq5331453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5331453
  have eq5331741 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5331166 eq5331456
    | exact resolve eq5331456 eq5331166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5331166 eq5331456
  have eq5331742 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq5331741
  have eq5331747 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5331742
       grind)
    | exact superpose eq5331742 eq10
    | exact resolve eq10 eq5331742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5331742
  have eq5331892 : x = y ∨ x = y := by
    first
    | (have i₁ := eq5331747
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5331747
    | exact resolve eq5331747 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5331747
  have eq5331893 : x = y := by grind
  clear eq5331892
  have eq5331896 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5331893
       grind)
    | exact superpose eq5331893 eq16
    | exact resolve eq16 eq5331893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5331893
  have eq5331897 : False := by grind
  exact eq5331897

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_y_pyx_y_pyx_Equation630 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq265 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ y) (σ x)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
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
  have eq273 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq268 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq274 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq273 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq278 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq274 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq274 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq274 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq281 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq265
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq265 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq282 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq281
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq281
    | exact resolve eq281 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq401 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq278 X0 (τ X1)
       grind)
    | exact superpose eq278 eq17
    | (have j1 := eq278 X0 (τ X1)
       grind)
    | exact resolve eq17 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq407 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq278 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq841 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq401 (τ X0) X1
       grind)
    | exact superpose eq401 eq18
    | (have j1 := eq401 (τ X0) X1
       grind)
    | exact resolve eq18 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq401
  have eq846 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq841 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq841
    | (have j0 := eq841 X0 X1
       grind)
    | exact resolve eq841 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq860 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq846 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq846
    | (have j0 := eq846 X0 X1
       grind)
    | exact resolve eq846 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq863 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq860 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq860
    | (have j0 := eq860 X0 X1
       grind)
    | exact resolve eq860 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq924 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq863 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq863
    | (have j0 := eq863 X1 (σ X0)
       grind)
    | exact resolve eq863 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq1242 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq924 X0 X0
       have i₂ := eq278 X0 (σ X0)
       grind)
    | exact superpose eq278 eq924
    | (have j0 := eq924 X1 X0
       have j1 := eq278 X0 (σ X1)
       grind)
    | exact resolve eq924 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq924
  have eq1272 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1242 X0 X1
       have j1 := eq407 (σ X1) X0
       grind)
    | (have r₁ := eq1242 X1 X1
       have r₂ := eq407 (σ X1) X1
       grind)
    | exact resolve eq1242 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407 eq1242
  have eq1455 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq1272 (σ X0) X1
       grind)
    | exact superpose eq1272 eq22
    | (have j1 := eq1272 (σ X0) X1
       grind)
    | exact resolve eq22 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1272
  have eq1462 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1455 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1455
    | (have j0 := eq1455 X0 X1
       grind)
    | exact resolve eq1455 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1455
  have eq1478 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1462 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1462
    | (have j0 := eq1462 X0 X1
       grind)
    | exact resolve eq1462 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1462
  have eq1487 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1478 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1478
    | (have j0 := eq1478 X0 X1
       grind)
    | exact resolve eq1478 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478
  have eq1573 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1487 x y
       grind)
    | exact superpose eq1487 eq16
    | (have j1 := eq1487 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1487 x y
       grind)
    | exact resolve eq16 eq1487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1487
  have eq1596 : x = (k y x) := by grind
  clear eq1573
  have eq1868 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq282
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq282
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq282 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1869 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op y x) ∨ (M.op x y) = (k y x) := by grind
  clear eq1868
  have eq1870 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq1869
       have r₂ := eq12 y x
       grind)
    | exact resolve eq1869 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869
  have eq1871 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1870
       have i₂ := eq1596
       grind)
    | exact superpose eq1596 eq1870
    | exact resolve eq1870 eq1596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1870
  have eq1872 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1871
       have i₂ := eq1596
       grind)
    | exact superpose eq1596 eq1871
    | exact resolve eq1871 eq1596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1871
  have eq1873 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq282
       have i₂ := eq1872
       grind)
    | exact superpose eq1872 eq282
    | exact resolve eq282 eq1872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282 eq1872
  have eq1881 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1873
  have eq1882 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1881
       have i₂ := eq1596
       grind)
    | exact superpose eq1596 eq1881
    | exact resolve eq1881 eq1596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1881
  have eq1883 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1882
  have eq1885 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1883
       grind)
    | exact superpose eq1883 eq16
    | exact resolve eq16 eq1883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883
  have eq1904 : (σ x) ≠ (σ x) ∨ x = (M.op y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1885
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq1885
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq1885 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1905 : x = (M.op y x) ∨ (M.op x y) = (k y x) := by grind
  clear eq1904
  have eq1907 : (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq1905
       have r₂ := eq12 y x
       grind)
    | exact resolve eq1905 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1905
  have eq1908 : x = (M.op x y) := by
    first
    | (have i₁ := eq1907
       have i₂ := eq1596
       grind)
    | exact superpose eq1596 eq1907
    | exact resolve eq1907 eq1596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596 eq1907
  have eq1909 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1885
       have i₂ := eq1908
       grind)
    | exact superpose eq1908 eq1885
    | exact resolve eq1885 eq1908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885 eq1908
  have eq1919 : False := by grind
  exact eq1919
