import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxy_x_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
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
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq15
    | exact resolve eq15 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq70 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq70
    | exact resolve eq70 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq70
  have eq95 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq81 X0
       grind)
    | exact superpose eq81 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq560 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq543 X0 X1
       have i₂ := eq81 X1
       grind)
    | exact superpose eq81 eq543
    | (have j0 := eq543 X0 X1
       grind)
    | exact resolve eq543 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq2933 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq560 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq560
    | exact resolve eq560 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq3011 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2933 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq2933
    | (have j0 := eq2933 X0 X1
       grind)
    | exact resolve eq2933 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2933
  have eq3018 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3011 X0 X1
       have j1 := eq95 X1 X0
       grind)
    | (have r₁ := eq3011 X1 X0
       have r₂ := eq95 X0 X1
       grind)
    | (have r₁ := eq3011 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq3011 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq3011
  have eq3024 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3018 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3018
    | exact resolve eq3018 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3049 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3018 (σ X0) X1
       grind)
    | exact superpose eq3018 eq15
    | (have j1 := eq3018 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq3018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3018
  have eq3102 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq3024 (τ X1) X0
       grind)
    | exact superpose eq3024 eq19
    | (have j1 := eq3024 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq3024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3024
  have eq3421 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3102 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3102
    | exact resolve eq3102 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3102
  have eq3477 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3421 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3421
    | (have j0 := eq3421 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq3421 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3421
  have eq3824 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3049 x y
       grind)
    | exact superpose eq3049 eq16
    | (have j1 := eq3049 x y
       grind)
    | exact resolve eq16 eq3049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3049
  have eq3852 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3824
       have i₂ := eq3477 y x
       grind)
    | exact superpose eq3477 eq3824
    | (have j1 := eq3477 (σ x) (σ y)
       grind)
    | (have r₁ := eq3824
       have r₂ := eq3477 y x
       grind)
    | (have r₁ := eq3824
       have r₂ := eq3477 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq3824
       have r₂ := eq3477 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3824 eq3477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3477 eq3824
  have eq3853 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq3852
  have eq3856 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3853
       grind)
    | exact superpose eq3853 eq16
    | exact resolve eq16 eq3853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3853
  have eq3857 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq3856
       have r₂ := eq81 x
       grind)
    | exact resolve eq3856 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3856
  have eq3858 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3857
       grind)
    | exact superpose eq3857 eq16
    | exact resolve eq16 eq3857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3859 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3857
       grind)
    | exact superpose eq3857 eq10
    | exact resolve eq10 eq3857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3857
  have eq3910 : x = y := by
    first
    | (have i₁ := eq3859
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3859
    | exact resolve eq3859 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3859
  have eq3911 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq3858
       have i₂ := eq81 x
       grind)
    | exact superpose eq81 eq3858
    | exact resolve eq3858 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq3858
  have eq3912 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq3911
       have i₂ := eq3910
       grind)
    | exact superpose eq3910 eq3911
    | exact resolve eq3911 eq3910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3910 eq3911
  have eq3913 : False := by grind
  exact eq3913

/-- `Equation4494`: `x ◇ (y ◇ y) = (z ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_x_pxx_pxy_Equation4494 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4494 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4494.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
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
  have eq180 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq180 eq202
    | exact resolve eq202 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq202
  have eq244 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq203 eq13
    | (have j0 := eq13 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq203 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact resolve eq13 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq247 : ∀ X0 : G, (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq244 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq507 : (M.op x y) = (k x y) ∨ x = y ∨ y = (M.op y y) := by
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
  have eq516 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq540 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq801 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    intro X0
    first
    | exact superpose eq247 eq706
    | exact resolve eq706 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq706
  have eq835 : ∀ X0 : G, (k X0 (τ (M.op (M.op (σ x) (σ y)) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq801 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq801
    | exact resolve eq801 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq1575 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq540 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1714 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq507
       grind)
    | exact superpose eq507 eq40
    | exact resolve eq40 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq507
  have eq1715 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1714
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1714
    | exact resolve eq1714 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1714
  have eq1717 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1715
    | exact resolve eq1715 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1715
  have eq2087 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq1717 eq516
    | exact resolve eq516 eq1717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516 eq1717
  have eq2094 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq2087
       have r₂ := eq27
       grind)
    | exact resolve eq2087 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2087
  have eq2109 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq2094 eq16
    | exact resolve eq16 eq2094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2111 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq2094 eq2109
    | exact resolve eq2109 eq2094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2094 eq2109
  have eq2183 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq2111 eq835
    | exact resolve eq835 eq2111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2111
  have eq2225 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq31 eq2183
    | exact resolve eq2183 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2183
  have eq2235 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq2225 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq2225 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq2225 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2225
  have eq2242 : y ≠ y ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1575 y
       have i₂ := eq2235 y
       grind)
    | exact superpose eq2235 eq1575
    | (have j0 := eq1575 y
       grind)
    | (have r₁ := eq1575 y
       have r₂ := eq2235 y
       grind)
    | exact resolve eq1575 eq2235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2247 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq2235 y
       grind)
    | exact superpose eq2235 eq36
    | exact resolve eq36 eq2235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq2235
  have eq2253 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2242
  have eq2260 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2247
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2247
    | exact resolve eq2247 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2247
  have eq2278 : ∀ X0 : G, (M.op y y) = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq2253
       grind)
    | exact superpose eq2253 eq16
    | exact resolve eq16 eq2253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2280 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2253 eq2278
    | exact resolve eq2278 eq2253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2253 eq2278
  have eq2290 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2260 eq1575
    | (have j0 := eq1575 (σ y)
       grind)
    | (have r₁ := eq1575 (σ y)
       have r₂ := eq2260
       grind)
    | exact resolve eq1575 eq2260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1575 eq2260
  have eq2291 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2290
  have eq2615 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq2280 x
       grind)
    | exact superpose eq2280 eq18
    | (have j1 := eq2280 x
       grind)
    | exact resolve eq18 eq2280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2280
  have eq2697 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2615 eq31
    | exact resolve eq31 eq2615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2615
  have eq2767 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq2697
    | exact resolve eq2697 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2697
  have eq2768 : y = (M.op x y) ∨ x = y := by grind
  clear eq2767
  have eq2770 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq2768
       grind)
    | exact superpose eq2768 eq24
    | exact resolve eq24 eq2768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2768
  have eq2835 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq2770
    | exact resolve eq2770 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2770
  have eq2905 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2291 eq16
    | exact resolve eq16 eq2291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2916 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2291 eq2905
    | exact resolve eq2905 eq2291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2291 eq2905
  have eq2951 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2916 eq26
    | (have j1 := eq2916 (σ x)
       grind)
    | exact resolve eq26 eq2916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2916
  have eq3031 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2951 eq27
    | exact resolve eq27 eq2951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2951
  have eq3116 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq3031
       have r₂ := eq2835
       grind)
    | exact resolve eq3031 eq2835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2835 eq3031
  have eq3138 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq3116 eq31
    | exact resolve eq31 eq3116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3116
  have eq3209 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq3138
    | exact resolve eq3138 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3138
  have eq3210 : x = y := by grind
  clear eq3209
  have eq3222 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3210
       grind)
    | exact superpose eq3210 eq18
    | exact resolve eq18 eq3210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3223 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3210
       grind)
    | exact superpose eq3210 eq24
    | exact resolve eq24 eq3210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3210
  have eq3277 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3223
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3223
    | exact resolve eq3223 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3223
  have eq3278 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3277 eq26
    | exact resolve eq26 eq3277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq3311 : ∀ X0 : G, (k X0 (τ (M.op (M.op (σ x) (σ y)) (σ x)))) = X0 := by
    intro X0
    first
    | exact superpose eq3277 eq835
    | exact resolve eq835 eq3277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835 eq3277
  have eq3350 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq3222
       grind)
    | exact superpose eq3222 eq13
    | (have j0 := eq13 X0 x
       grind)
    | exact resolve eq13 eq3222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3355 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq540 x
       have i₂ := eq3222
       grind)
    | exact superpose eq3222 eq540
    | exact resolve eq540 eq3222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3222
  have eq3372 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3278 eq540
    | exact resolve eq540 eq3278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq4441 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq3355
       grind)
    | exact superpose eq3355 eq39
    | exact resolve eq39 eq3355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq4444 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4441
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4441
    | exact resolve eq4441 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4441
  have eq4446 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4444
    | exact resolve eq4444 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4444
  have eq4457 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4446 eq3372
    | exact resolve eq3372 eq4446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4446
  have eq4467 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4457
       have r₂ := eq27
       grind)
    | exact resolve eq4457 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4457
  have eq4518 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (σ x)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4467 eq3311
    | exact resolve eq3311 eq4467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3311
  have eq4527 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (σ y)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3278 eq4518
    | exact resolve eq4518 eq3278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3278 eq4518
  have eq4572 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4467 eq4527
    | exact resolve eq4527 eq4467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4467 eq4527
  have eq4616 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq4572
    | exact resolve eq4572 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4572
  have eq4642 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq4616 X0
       have j1 := eq3350 X0
       grind)
    | (have r₁ := eq4616 X0
       have r₂ := eq3350 X0
       grind)
    | exact resolve eq4616 eq3350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3350 eq4616
  have eq4662 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3355
       have i₂ := eq4642 x
       grind)
    | exact superpose eq4642 eq3355
    | exact resolve eq3355 eq4642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3355
  have eq4663 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq4642 x
       grind)
    | exact superpose eq4642 eq35
    | exact resolve eq35 eq4642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq4642
  have eq4669 : x = (M.op x y) := by grind
  clear eq4662
  have eq4678 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq4663
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4663
    | exact resolve eq4663 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4663
  have eq5037 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq4669
       grind)
    | exact superpose eq4669 eq22
    | exact resolve eq22 eq4669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4669
  have eq5189 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5037 eq20
    | exact resolve eq20 eq5037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5037
  have eq5285 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4678 eq3372
    | exact resolve eq3372 eq4678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3372 eq4678
  have eq5293 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5285
  have eq5298 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq5293 eq27
    | exact resolve eq27 eq5293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq5293
  have eq5397 : False := by grind
  exact eq5397

/-- `Equation4502`: `x ◇ (y ◇ y) = (z ◇ w) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_x_pxy_Equation4502 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4502 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4502.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq13 X0 (k (M.op X0 X0) X1)
       grind)
    | exact resolve eq12 eq13
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq91 (M.op sF2 sF2)
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq91
    | exact resolve eq91 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq200 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq30 eq189
    | exact resolve eq189 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq189
  have eq207 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq108 (M.op sF3 sF3)
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq108
    | exact resolve eq108 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq218 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq207
    | exact resolve eq207 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq397 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq693 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) X1) := by
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
  have eq694 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x x
       have i₂ := eq16 X2 X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq705 : ∀ X0 X2 X3 : G, (M.op (M.op x y) X0) = (M.op (M.op X2 X3) X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 x X0 X2 X3
       have i₂ := eq693 x X0
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op (M.op X2 X3) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X2 X3
       have i₂ := eq693 (M.op X0 X0) X0
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq175 (M.op X0 X0)
       have i₂ := eq693 (M.op X0 X0) X0
       grind)
    | exact superpose eq693 eq175
    | exact resolve eq175 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq713 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq706 X0 X1 x x
       have i₂ := eq694 (M.op x x) X0
       grind)
    | exact superpose eq694 eq706
    | exact resolve eq706 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq723 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq693 x X0
       have i₂ := eq694 x X0
       grind)
    | exact superpose eq694 eq693
    | exact resolve eq693 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq726 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op X0 X0)) = (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X2 X3
       have i₂ := eq694 (M.op X0 X0) X0
       grind)
    | exact superpose eq694 eq16
    | exact resolve eq16 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq733 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq726 X0 X1 x x
       have i₂ := eq694 (M.op x x) X0
       grind)
    | exact superpose eq694 eq726
    | exact resolve eq726 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq741 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op X1 (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq723 eq733
    | exact resolve eq733 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq797 : ∀ X0 X1 : G, (M.op (M.op x y) X0) ≠ (M.op (M.op (σ x) (σ y)) X0) ∨ (k X1 (M.op (M.op x y) X0)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq713 eq28
    | (have j0 := eq28 X1 (M.op (M.op x y) X0)
       grind)
    | exact resolve eq28 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq806 : ∀ X0 X1 : G, (k X1 (M.op (M.op x y) X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq797 X0 X1
       grind)
    | (have r₁ := eq797 X0 X1
       have r₂ := eq723 X0
       grind)
    | exact resolve eq797 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq827 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op x y) X1))) := by
    intro X0 X1
    first
    | exact superpose eq806 eq397
    | exact resolve eq397 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq828 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op x y) X1))) := by
    intro X0 X1
    first
    | exact superpose eq806 eq35
    | exact resolve eq35 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq806
  have eq841 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op x y) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq828 X0 X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq828
    | exact resolve eq828 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq842 : ∀ X0 X1 : G, (k X0 (τ (M.op (M.op x y) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq827 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq827
    | exact resolve eq827 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq856 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op X1 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq693 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq693
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq693 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq859 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq28
    | (have j0 := eq28 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq28 X0 (M.op X0 X0)
       have r₂ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq862 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (k X0 (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq693 X0 X1
       have i₂ := eq11 X0 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq693
    | (have j1 := eq11 (M.op X1 X1) (M.op X1 X1)
       grind)
    | exact resolve eq693 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq871 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq879 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq884 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq885 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq884 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884
  have eq896 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq859 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq899 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op X1 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq856 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq915 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (σ x) (σ y)) X1) ∨ (M.op (M.op x y) X1) = (k X0 (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq862 X0 X1
       have i₂ := eq694 (M.op X1 X1) X1
       grind)
    | exact superpose eq694 eq862
    | (have j0 := eq862 X0 X1
       grind)
    | exact resolve eq862 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694 eq862
  have eq917 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq896 X0 X1
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq896 X1 X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq896 X1 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq896 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq935 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (k X0 (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op (M.op x y) X1) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | exact superpose eq723 eq915
    | (have j0 := eq915 X0 X1
       grind)
    | exact resolve eq915 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq1039 : ∀ X0 : G, (σ (M.op (M.op x y) X0)) ≠ (σ (M.op (M.op x y) X0)) ∨ (σ (M.op (M.op x y) X0)) = (M.op (σ (M.op (M.op x y) X0)) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq841 eq885
    | (have j0 := eq885 (σ (M.op (M.op x y) X0))
       grind)
    | (have r₁ := eq885 (σ (M.op (M.op x y) x))
       have r₂ := eq841 (σ (M.op (M.op x y) x)) x
       grind)
    | exact resolve eq885 eq841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq1052 : ∀ X0 : G, (σ (M.op (M.op x y) X0)) = (M.op (σ (M.op (M.op x y) X0)) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | (have j0 := eq1039 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq1079 : ∀ X0 : G, (τ (M.op (M.op x y) X0)) ≠ (τ (M.op (M.op x y) X0)) ∨ (τ (M.op (M.op x y) X0)) = (M.op (τ (M.op (M.op x y) X0)) (τ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq842 eq885
    | (have j0 := eq885 (τ (M.op (M.op x y) X0))
       grind)
    | (have r₁ := eq885 (τ (M.op (M.op x y) x))
       have r₂ := eq842 (τ (M.op (M.op x y) x)) x
       grind)
    | exact resolve eq885 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq1089 : ∀ X0 : G, (τ (M.op (M.op x y) X0)) = (M.op (τ (M.op (M.op x y) X0)) (τ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | (have j0 := eq1079 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079
  have eq3036 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq871
       grind)
    | exact superpose eq871 eq41
    | exact resolve eq41 eq871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3037 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3036
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3036
    | exact resolve eq3036 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3036
  have eq3039 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq3037
    | exact resolve eq3037 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3037
  have eq20876 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (σ (M.op (M.op x y) X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq1052 eq705
    | exact resolve eq705 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20926 : ∀ X0 : G, (σ (M.op (M.op x y) X0)) = (M.op (M.op x y) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq20876 eq1052
    | exact resolve eq1052 eq20876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052 eq20876
  have eq20998 : ∀ X0 X1 : G, (σ (M.op (M.op x y) X0)) = (M.op X1 (σ (M.op (M.op x y) X0))) := by
    intro X0 X1
    first
    | exact superpose eq20926 eq741
    | exact resolve eq741 eq20926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20926
  have eq22495 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (τ (M.op (M.op x y) X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq1089 eq705
    | exact resolve eq705 eq1089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq22562 : ∀ X0 : G, (τ (M.op (M.op x y) X0)) = (M.op (M.op x y) (τ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq22495 eq1089
    | exact resolve eq1089 eq22495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089 eq22495
  have eq22652 : ∀ X0 X1 : G, (τ (M.op (M.op x y) X0)) = (M.op X1 (τ (M.op (M.op x y) X0))) := by
    intro X0 X1
    first
    | exact superpose eq22562 eq741
    | exact resolve eq741 eq22562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22562
  have eq26466 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3039 eq879
    | exact resolve eq879 eq3039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3039
  have eq26473 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq26466
       have r₂ := eq27
       grind)
    | exact resolve eq26466 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26466
  have eq26480 : y = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26473 eq218
    | exact resolve eq218 eq26473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26473
  have eq26513 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq26480
    | exact resolve eq26480 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26480
  have eq26517 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq26513
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq26513
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq26513
       have r₂ := eq13 x y
       grind)
    | exact resolve eq26513 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26513
  have eq26519 : x = (k x (τ (σ y))) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26517 eq200
    | exact resolve eq200 eq26517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq26517
  have eq26556 : x = (k x y) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq26519
    | exact resolve eq26519 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26519
  have eq26560 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq917 y x
       grind)
    | (have r₁ := eq26556
       have r₂ := eq917 y x
       grind)
    | exact resolve eq26556 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26556
  have eq26561 : x = (k x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq26560
       have r₂ := eq13 x y
       grind)
    | exact resolve eq26560 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26560
  have eq26565 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq871
       have i₂ := eq26561
       grind)
    | exact superpose eq26561 eq871
    | exact resolve eq871 eq26561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq26567 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq26561
       grind)
    | exact superpose eq26561 eq41
    | exact resolve eq41 eq26561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq26561
  have eq26568 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq26567
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26567
    | exact resolve eq26567 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26567
  have eq26578 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26568 eq879
    | exact resolve eq879 eq26568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879 eq26568
  have eq26592 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq28 X0 y
       have i₂ := eq26565
       grind)
    | exact superpose eq26565 eq28
    | (have j0 := eq28 X0 y
       grind)
    | (have r₁ := eq28 X0 y
       have r₂ := eq26565
       grind)
    | exact resolve eq28 eq26565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq26596 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq695 X0 y x
       have i₂ := eq26565
       grind)
    | exact superpose eq26565 eq695
    | exact resolve eq695 eq26565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26611 : ∀ X0 : G, y = (M.op x x) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq26592 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26592
  have eq26672 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26578 eq695
    | exact resolve eq695 eq26578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26733 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq693 X0 x
       have i₂ := eq26611 X1
       grind)
    | exact superpose eq26611 eq693
    | (have j1 := eq26611 X1
       grind)
    | exact resolve eq693 eq26611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26611
  have eq28683 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq26596 x X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq26596 X0 x
       grind)
    | exact superpose eq26596 eq18
    | (have j1 := eq26596 x X0
       grind)
    | exact resolve eq18 eq26596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26596
  have eq28917 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq26565
       have i₂ := eq28683 y
       grind)
    | exact superpose eq28683 eq26565
    | exact resolve eq26565 eq28683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26565 eq28683
  have eq29002 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq28917
  have eq29083 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq693 X0 x
       have i₂ := eq29002
       grind)
    | exact superpose eq29002 eq693
    | exact resolve eq693 eq29002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29741 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq29083 x
       grind)
    | (have i₁ := eq18
       have i₂ := eq29083 x
       grind)
    | exact superpose eq29083 eq18
    | (have j1 := eq29083 x
       grind)
    | exact resolve eq18 eq29083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29967 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29741 eq29083
    | exact resolve eq29083 eq29741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29083
  have eq30031 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29741 eq20998
    | exact resolve eq20998 eq29741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30056 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq29967 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29967
  have eq30065 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq30031
    | (have j0 := eq30031 X0
       grind)
    | exact resolve eq30031 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30031
  have eq31378 : ∀ X0 : G, (k X0 y) = (M.op (M.op x y) x) ∨ y = (M.op (M.op x y) x) ∨ (M.op X0 X0) = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq935 X0 x
       have i₂ := eq29002
       grind)
    | exact superpose eq29002 eq935
    | exact resolve eq935 eq29002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935 eq29002
  have eq31467 : ∀ X0 : G, (M.op x y) = (k X0 y) ∨ y = (M.op (M.op x y) x) ∨ (M.op X0 X0) = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29741 eq31378
    | (have j0 := eq31378 X0
       grind)
    | exact resolve eq31378 eq29741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31378
  have eq31477 : ∀ X0 : G, (M.op x y) = (k X0 y) ∨ y = (M.op x y) ∨ (M.op X0 X0) = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29741 eq31467
    | (have j0 := eq31467 X0
       grind)
    | exact resolve eq31467 eq29741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31467
  have eq31478 : ∀ X0 : G, (M.op x y) = (k X0 y) ∨ y = (M.op x y) ∨ (M.op X0 X0) = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq31477 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31477
  have eq44904 : ∀ X0 X1 : G, (τ (M.op X0 (σ y))) = (M.op X1 (τ (M.op X0 (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26672 eq22652
    | exact resolve eq22652 eq26672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22652
  have eq44912 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq26672 eq26
    | (have j1 := eq26672 (σ x) X0
       grind)
    | exact resolve eq26 eq26672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44915 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq26672 eq26578
    | exact resolve eq26578 eq26672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26578 eq26672
  have eq44923 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq44915 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44915
  have eq44937 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44923 eq44912
    | (have j1 := eq44923 (σ x)
       grind)
    | exact resolve eq44912 eq44923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44912
  have eq44943 : ∀ X1 : G, (τ (σ y)) = (M.op X1 (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X1
    first
    | exact superpose eq44923 eq44904
    | exact resolve eq44904 eq44923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44904 eq44923
  have eq45143 : ∀ X1 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op X1 y) := by
    intro X1
    first
    | exact superpose eq32 eq44943
    | exact resolve eq44943 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44943
  have eq45252 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq44937 eq693
    | exact resolve eq693 eq44937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44937
  have eq45344 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | exact superpose eq45143 eq693
    | (have j1 := eq45143 X1
       grind)
    | exact resolve eq693 eq45143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq45346 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op X2 y) := by
    intro X0 X1 X2
    first
    | exact superpose eq45143 eq695
    | (have j1 := eq45143 X2
       grind)
    | exact resolve eq695 eq45143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695 eq45143
  have eq45559 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45252 eq26
    | (have j1 := eq45252 (σ x)
       grind)
    | exact resolve eq26 eq45252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45252
  have eq51419 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq26733 x X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq26733 X0 x
       grind)
    | exact superpose eq26733 eq18
    | (have j1 := eq26733 x X0
       grind)
    | exact resolve eq18 eq26733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26733
  have eq51725 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq29741 eq51419
    | exact resolve eq51419 eq29741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29741 eq51419
  have eq51861 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) ∨ (k X1 (M.op x y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq741 X0 X1
       have i₂ := eq51725 (M.op sF0 X0)
       grind)
    | exact superpose eq51725 eq741
    | (have j1 := eq51725 X1
       grind)
    | exact resolve eq741 eq51725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741 eq51725
  have eq52091 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq707 X0
       have i₂ := eq51861 X0 (M.op sF0 X0)
       grind)
    | exact superpose eq51861 eq707
    | (have j1 := eq51861 X0 (M.op x y)
       grind)
    | exact resolve eq707 eq51861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707 eq51861
  have eq52230 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq52091 X0
       have j1 := eq917 (M.op x y) X0
       grind)
    | (have r₁ := eq52091 X0
       have r₂ := eq917 (M.op x y) x
       grind)
    | (have r₁ := eq52091 (M.op x y)
       have r₂ := eq917 (M.op x y) x
       grind)
    | exact resolve eq52091 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917 eq52091
  have eq52248 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq52230 eq885
    | (have j0 := eq885 (M.op x y)
       grind)
    | (have r₁ := eq885 (M.op x y)
       have r₂ := eq52230 (M.op x y)
       grind)
    | exact resolve eq885 eq52230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885 eq52230
  have eq52311 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq52248
  have eq52463 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq52311 eq20998
    | exact resolve eq20998 eq52311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52311
  have eq52513 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq52463
    | (have j0 := eq52463 X0
       grind)
    | exact resolve eq52463 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52463
  have eq138208 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq45344 eq26
    | (have j1 := eq45344 (σ x) X0
       grind)
    | exact resolve eq26 eq45344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45344
  have eq144605 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | exact superpose eq45346 eq26
    | (have j1 := eq45346 (σ x) X0 X1
       grind)
    | exact resolve eq26 eq45346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45346
  have eq213451 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq31478 y
       grind)
    | exact superpose eq31478 eq37
    | (have j1 := eq31478 y
       grind)
    | exact resolve eq37 eq31478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq31478
  have eq213477 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq213451
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq213451
    | exact resolve eq213451 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213451
  have eq213522 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq213477
    | exact resolve eq213477 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213477
  have eq213560 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30056 eq213522
    | exact resolve eq213522 eq30056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213522
  have eq213561 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq213560
  have eq213663 : (τ (σ (M.op x y))) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq213561 eq116
    | exact resolve eq116 eq213561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq213676 : ∀ X0 : G, (M.op (M.op x y) (σ y)) = (M.op X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq213561 eq899
    | (have j0 := eq899 (σ y) x
       grind)
    | exact resolve eq899 eq213561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899 eq213561
  have eq213692 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30065 eq213676
    | exact resolve eq213676 eq30065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30065 eq213676
  have eq213697 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq213663
    | exact resolve eq213663 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq213663
  have eq260569 : y = (k y (τ (σ y))) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq213692 eq218
    | exact resolve eq218 eq213692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq213692
  have eq260722 : y = (k y y) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq260569
    | exact resolve eq260569 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq260569
  have eq260743 : y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq213697 eq260722
    | exact resolve eq260722 eq213697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213697 eq260722
  have eq260744 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq260743
  have eq260936 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op X0 y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq260744 eq144605
    | (have j0 := eq144605 X0 X0
       grind)
    | exact resolve eq144605 eq260744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144605
  have eq260968 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op X0 y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq260936 X0
       grind)
    | (have r₁ := eq260936 X0
       have r₂ := eq27
       grind)
    | exact resolve eq260936 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260936
  have eq261054 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30056 eq260968
    | (have j0 := eq260968 x
       grind)
    | exact resolve eq260968 eq30056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30056 eq260968
  have eq261055 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq261054
  have eq261066 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq261055 eq723
    | exact resolve eq723 eq261055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq261055
  have eq261491 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq261066 eq26
    | (have j1 := eq261066 (σ y)
       grind)
    | exact resolve eq26 eq261066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261066
  have eq262132 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq260744 eq261491
    | exact resolve eq261491 eq260744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260744 eq261491
  have eq262167 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq262132
       have r₂ := eq27
       grind)
    | exact resolve eq262132 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262132
  have eq262171 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq262167
       grind)
    | exact superpose eq262167 eq24
    | exact resolve eq24 eq262167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262167
  have eq262465 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq262171
    | exact resolve eq262171 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262171
  have eq262642 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq262465 eq52513
    | exact resolve eq52513 eq262465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52513
  have eq262728 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq262642 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262642
  have eq266384 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq262728 eq26
    | (have j1 := eq262728 (σ x)
       grind)
    | exact resolve eq26 eq262728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq262728
  have eq266648 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq266384 eq27
    | exact resolve eq27 eq266384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266384
  have eq266817 : x = (M.op x y) := by
    first
    | (have r₁ := eq266648
       have r₂ := eq262465
       grind)
    | exact resolve eq266648 eq262465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262465 eq266648
  have eq266828 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq266817
       grind)
    | exact superpose eq266817 eq18
    | exact resolve eq18 eq266817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq266829 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq266817
       grind)
    | exact superpose eq266817 eq22
    | exact resolve eq22 eq266817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq266817
  have eq266943 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq266829 eq20
    | exact resolve eq20 eq266829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267908 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq266828 eq20998
    | exact resolve eq20998 eq266828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20998
  have eq268054 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq267908
    | (have j0 := eq267908 X0
       grind)
    | exact resolve eq267908 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq267908
  have eq268093 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq266943 eq268054
    | exact resolve eq268054 eq266943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268054
  have eq269152 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq268093 eq45559
    | exact resolve eq45559 eq268093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45559
  have eq269158 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq268093 eq138208
    | (have j0 := eq138208 X0
       grind)
    | exact resolve eq138208 eq268093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138208 eq268093
  have eq269269 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq269158 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269158
  have eq269274 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq269152
  have eq270903 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq269274
  have eq282462 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq266828
       have i₂ := eq269269 sF0
       grind)
    | exact superpose eq269269 eq266828
    | (have j1 := eq269269 x
       grind)
    | exact resolve eq266828 eq269269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266828 eq269269
  have eq282742 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq282462 eq27
    | exact resolve eq27 eq282462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282462
  have eq282770 : y = (M.op x y) := by
    first
    | (have r₁ := eq282742
       have r₂ := eq266943
       grind)
    | exact resolve eq282742 eq266943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282742
  have eq282775 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq282770
       grind)
    | exact superpose eq282770 eq24
    | exact resolve eq24 eq282770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq282770
  have eq282977 : (σ x) = (σ y) := by
    first
    | exact superpose eq266829 eq282775
    | exact resolve eq282775 eq266829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266829 eq282775
  have eq283226 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq282977 eq270903
    | (have r₁ := eq270903
       have r₂ := eq282977
       grind)
    | exact resolve eq270903 eq282977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270903 eq282977
  have eq283229 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq283226
  have eq283497 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq283229 eq27
    | exact resolve eq27 eq283229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq283229
  have eq283524 : False := by grind
  exact eq283524

/-- `Equation4503`: `x ◇ (y ◇ y) = (z ◇ w) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_x_pxy_Equation4503 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4503 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4503.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X2) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq13 X0 (k (M.op X0 X0) X1)
       grind)
    | exact resolve eq12 eq13
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq38 (M.op sF0 sF0)
       have i₂ := eq175 sF0
       grind)
    | exact superpose eq175 eq38
    | exact resolve eq38 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq179 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq178
    | exact resolve eq178 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq189 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq91 (M.op sF2 sF2)
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq91
    | exact resolve eq91 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq200 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq30 eq189
    | exact resolve eq189 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq207 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq108 (M.op sF3 sF3)
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq108
    | exact resolve eq108 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq175
  have eq218 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq207
    | exact resolve eq207 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq689 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X4 X5) X4) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq16 x x X4 X5
       have i₂ := eq16 x x X0 X1
       grind)
    | (have i₁ := eq16 (M.op (M.op X1 X1) x) X1 x x
       have i₂ := eq16 X0 X1 (M.op X1 X1) x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X0) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X2 X3 X4 (M.op x x)
       have i₂ := eq16 X4 x X0 X1
       grind)
    | (have i₁ := eq16 X0 X1 (M.op X2 X3) X2
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) x) := by
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
  have eq694 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq701 : ∀ X0 X1 X4 : G, (M.op (M.op (M.op X0 X1) X0) X4) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq691 X0 X1 x x X4
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq691
    | exact resolve eq691 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq703 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq693 X0 (M.op x x)
       have i₂ := eq693 (M.op x x) x
       grind)
    | exact superpose eq693 eq693
    | exact resolve eq693 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : ∀ X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op x y) x) := by
    intro X2 X3
    first
    | (have i₁ := eq16 x x X2 X3
       have i₂ := eq693 x x
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op X0 (M.op (M.op x y) x)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op x x) X2 X3
       have i₂ := eq693 (M.op x x) x
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq712 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (M.op x y) x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2 (M.op x x)
       have i₂ := eq693 X2 x
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq714 : ∀ X2 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op x y) x) X2) := by
    intro X2
    first
    | (have i₁ := eq712 x x X2
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq712
    | exact resolve eq712 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq722 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq693 x x
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq693
    | exact resolve eq693 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq729 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2 (M.op x x)
       have i₂ := eq694 X2 x
       grind)
    | exact superpose eq694 eq16
    | exact resolve eq16 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq731 : ∀ X2 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X2) := by
    intro X2
    first
    | (have i₁ := eq729 x x X2
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq729
    | exact resolve eq729 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq738 : ∀ X2 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) X2) := by
    intro X2
    first
    | exact superpose eq722 eq731
    | exact resolve eq731 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq747 : ∀ X0 : G, (M.op (M.op x y) x) ≠ (M.op (M.op x y) x) ∨ (k X0 (M.op (M.op x y) x)) = X0 := by
    intro X0
    first
    | exact superpose eq703 eq28
    | (have j0 := eq28 X0 (M.op (M.op x y) x)
       grind)
    | (have r₁ := eq28 X0 (M.op (M.op x y) x)
       have r₂ := eq703 (M.op (M.op x y) x)
       grind)
    | exact resolve eq28 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq751 : ∀ X0 : G, (k X0 (M.op (M.op x y) x)) = X0 := by
    intro X0
    first
    | (have j0 := eq747 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq755 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op x y) x))) := by
    intro X0
    first
    | exact superpose eq751 eq35
    | exact resolve eq35 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq768 : ∀ X0 : G, (k X0 (σ (M.op (M.op x y) x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq755 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq755
    | exact resolve eq755 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq790 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq28
    | (have j0 := eq28 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq28 X0 (M.op X0 X0)
       have r₂ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq796 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X3)) = (M.op (k X0 X1) X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X1 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq797 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X3)) = (k (M.op X0 X1) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 X0 X1
       have i₂ := eq11 (M.op X0 X1) X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq800 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq809 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq814 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq815 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq814 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq826 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq790 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq839 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op X0 X1) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq797 X0 X1 x x
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq797
    | (have j0 := eq797 X0 X1 x x
       grind)
    | exact resolve eq797 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq840 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (k X0 X1) X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq796 X0 X1 x x
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq796
    | (have j0 := eq796 X1 X1 x x
       grind)
    | exact resolve eq796 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694 eq796
  have eq844 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq826 X0 X1
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq826 X1 X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq826 X1 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq826 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq856 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (k (M.op X0 X1) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq722 eq839
    | (have j0 := eq839 X0 X1
       grind)
    | exact resolve eq839 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq857 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (k X0 X1) X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq722 eq840
    | (have j0 := eq840 X1 X1
       grind)
    | exact resolve eq840 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq908 : (σ (M.op (M.op x y) x)) ≠ (σ (M.op (M.op x y) x)) ∨ (σ (M.op (M.op x y) x)) = (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) := by
    first
    | exact superpose eq768 eq815
    | (have j0 := eq815 (σ (M.op (M.op x y) x))
       grind)
    | (have r₁ := eq815 (σ (M.op (M.op x y) x))
       have r₂ := eq768 (σ (M.op (M.op x y) x))
       grind)
    | exact resolve eq815 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq921 : (σ (M.op (M.op x y) x)) = (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) := by grind
  clear eq908
  have eq1007 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (M.op x y) x) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) = X0 := by
    intro X0
    first
    | exact superpose eq714 eq11
    | (have j0 := eq11 X0 X0
       grind)
    | exact resolve eq11 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq1010 : ∀ X0 : G, (M.op (M.op x y) x) = (k (M.op (M.op x y) x) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) = X0 := by
    intro X0
    first
    | exact superpose eq722 eq1007
    | (have j0 := eq1007 X0
       grind)
    | exact resolve eq1007 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1019 : ∀ X0 : G, (M.op (M.op x y) x) = (k (M.op (M.op x y) x) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1010 X0
       have j1 := eq13 (M.op (M.op x y) x) X0
       grind)
    | (have r₁ := eq1010 x
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq1010 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq1010 x
       have r₂ := eq13 (M.op (M.op x y) x) x
       grind)
    | exact resolve eq1010 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq1022 : ∀ X0 : G, (M.op (M.op x y) x) = (k (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | (have j0 := eq1019 X0
       have j1 := eq28 (M.op (M.op x y) x) X0
       grind)
    | (have r₁ := eq1019 x
       have r₂ := eq28 X0 x
       grind)
    | exact resolve eq1019 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq2736 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq800
       grind)
    | exact superpose eq800 eq41
    | exact resolve eq41 eq800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2737 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2736
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2736
    | exact resolve eq2736 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2736
  have eq2739 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq2737
    | exact resolve eq2737 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2737
  have eq6562 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (k (k X0 X1) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (k X0 X1) (k X0 X1)) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1) X0
       have i₂ := eq857 X0 X1
       grind)
    | exact superpose eq857 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq857 X0 X0
       grind)
    | exact resolve eq11 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq8769 : ∀ X0 : G, (σ (M.op (M.op x y) x)) = (k (σ (M.op (M.op x y) X0)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq42 (M.op sF0 x)
       have i₂ := eq856 sF0 x
       grind)
    | exact superpose eq856 eq42
    | (have j1 := eq856 (M.op x y) X0
       grind)
    | exact resolve eq42 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq21203 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 (σ (M.op (M.op x y) x))) := by
    intro X0
    first
    | exact superpose eq921 eq693
    | exact resolve eq693 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21224 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) x)) = (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) := by
    intro X0
    first
    | exact superpose eq921 eq708
    | exact resolve eq708 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq21227 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) x)) = (σ (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq921 eq21224
    | exact resolve eq21224 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921 eq21224
  have eq21242 : (M.op (M.op x y) x) = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq703 eq21227
    | exact resolve eq21227 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21227
  have eq21289 : (M.op (M.op x y) x) = (τ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq21242 eq15
    | exact resolve eq15 eq21242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23847 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2739 eq809
    | exact resolve eq809 eq2739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2739
  have eq23855 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq23847
       have r₂ := eq27
       grind)
    | exact resolve eq23847 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23847
  have eq23862 : y = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23855 eq218
    | exact resolve eq218 eq23855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq23855
  have eq23904 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq23862
    | exact resolve eq23862 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23862
  have eq23910 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq23904
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq23904
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq23904
       have r₂ := eq13 x y
       grind)
    | exact resolve eq23904 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23904
  have eq23913 : x = (k x (τ (σ y))) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23910 eq200
    | exact resolve eq200 eq23910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq23910
  have eq23957 : x = (k x y) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq23913
    | exact resolve eq23913 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23913
  have eq23963 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq844 y x
       grind)
    | (have r₁ := eq23957
       have r₂ := eq844 y x
       grind)
    | exact resolve eq23957 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq23957
  have eq23964 : x = (k x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq23963
       have r₂ := eq13 x y
       grind)
    | exact resolve eq23963 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23963
  have eq23968 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq800
       have i₂ := eq23964
       grind)
    | exact superpose eq23964 eq800
    | exact resolve eq800 eq23964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq23970 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq23964
       grind)
    | exact superpose eq23964 eq41
    | exact resolve eq41 eq23964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq23964
  have eq23972 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq23970
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23970
    | exact resolve eq23970 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23970
  have eq23982 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23972 eq809
    | exact resolve eq809 eq23972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809 eq23972
  have eq23999 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq693 X0 y
       have i₂ := eq23968
       grind)
    | exact superpose eq23968 eq693
    | exact resolve eq693 eq23968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24016 : (M.op y y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq707 y y
       have i₂ := eq23968
       grind)
    | exact superpose eq23968 eq707
    | exact resolve eq707 eq23968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24021 : y = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23968 eq24016
    | exact resolve eq24016 eq23968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23968 eq24016
  have eq24098 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq23982 eq28
    | (have j0 := eq28 X0 (σ y)
       grind)
    | (have r₁ := eq28 X0 (σ y)
       have r₂ := eq23982
       grind)
    | exact resolve eq28 eq23982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24100 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq23982 eq693
    | exact resolve eq693 eq23982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24115 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ y) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq23982 eq701
    | exact resolve eq701 eq23982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq24117 : (M.op (σ y) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23982 eq707
    | exact resolve eq707 eq23982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24119 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq24098 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24098
  have eq24122 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq23982 eq24117
    | exact resolve eq24117 eq23982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24117
  have eq24124 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (σ y) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq722 eq24115
    | exact resolve eq24115 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24115
  have eq24139 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq23982 eq24124
    | exact resolve eq24124 eq23982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23982 eq24124
  have eq24143 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq24122 eq24139
    | exact resolve eq24139 eq24122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24139
  have eq24301 : ∀ X0 : G, y = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq24021 eq21203
    | exact resolve eq21203 eq24021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21203
  have eq24303 : y = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq24021 eq21242
    | exact resolve eq21242 eq24021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24329 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq24303
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24303
    | exact resolve eq24303 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24303
  have eq24331 : ∀ X0 : G, y = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq24301 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24301
    | (have j0 := eq24301 X0
       grind)
    | exact resolve eq24301 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24301
  have eq24400 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq24329 eq24331
    | exact resolve eq24331 eq24329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24331
  have eq24589 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq693 X0 x
       have i₂ := eq24329
       grind)
    | exact superpose eq24329 eq693
    | exact resolve eq693 eq24329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24597 : y = (k x x) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq24329
       grind)
    | exact superpose eq24329 eq11
    | exact resolve eq11 eq24329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24329
  have eq24611 : y = (k x x) ∨ x = y ∨ x = (M.op x y) ∨ y = (σ y) := by grind
  clear eq24597
  have eq25405 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq693 X0 X1
       have i₂ := eq24119 (M.op X1 X1)
       grind)
    | exact superpose eq24119 eq693
    | (have j1 := eq24119 X1
       grind)
    | exact resolve eq693 eq24119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24119
  have eq25457 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq24122 eq693
    | exact resolve eq693 eq24122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26168 : (σ y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq24400 eq738
    | exact resolve eq738 eq24400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26174 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24400 eq26
    | (have j1 := eq24400 (σ x)
       grind)
    | exact resolve eq26 eq24400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24400
  have eq26260 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq693 X0 x
       have i₂ := eq26174
       grind)
    | exact superpose eq26174 eq693
    | exact resolve eq693 eq26174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26174
  have eq26306 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op x y) ∨ y = (σ y) ∨ x = (M.op x y) ∨ y = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq24589 eq24589
    | exact resolve eq24589 eq24589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26406 : ∀ X0 : G, (M.op X0 y) = (τ (M.op X0 y)) ∨ x = (M.op x y) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq24589 eq21289
    | exact resolve eq21289 eq24589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26462 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq24589 x
       grind)
    | (have i₁ := eq18
       have i₂ := eq24589 x
       grind)
    | exact superpose eq24589 eq18
    | (have j1 := eq24589 x
       grind)
    | exact resolve eq18 eq24589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24589
  have eq26476 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op x y) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have j0 := eq26306 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26306
  have eq26733 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq26462 eq703
    | exact resolve eq703 eq26462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26814 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq26462 eq21242
    | exact resolve eq21242 eq26462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26848 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq26814
    | exact resolve eq26814 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26814
  have eq33135 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq26260 x
       grind)
    | (have i₁ := eq18
       have i₂ := eq26260 x
       grind)
    | exact superpose eq26260 eq18
    | (have j1 := eq26260 x
       grind)
    | exact resolve eq18 eq26260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33434 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq33135 eq738
    | exact resolve eq738 eq33135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33516 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq33135 eq26260
    | exact resolve eq26260 eq33135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26260 eq33135
  have eq33532 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq33516 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33516
  have eq46698 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq24611
       grind)
    | exact superpose eq24611 eq40
    | exact resolve eq40 eq24611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq24611
  have eq46724 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq46698
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq46698
    | exact resolve eq46698 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46698
  have eq46734 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq46724
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq46724
    | exact resolve eq46724 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46724
  have eq48040 : (σ y) = (τ (σ y)) ∨ x = (M.op x y) ∨ y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq24143 eq26406
    | exact resolve eq26406 eq24143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26406
  have eq48135 : y = (σ y) ∨ x = (M.op x y) ∨ y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32 eq48040
    | exact resolve eq48040 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48040
  have eq48136 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq48135
  have eq53385 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq48136 eq693
    | exact resolve eq693 eq48136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48136
  have eq53427 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq26462 eq53385
    | exact resolve eq53385 eq26462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53385
  have eq60462 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq53427 eq26
    | (have j1 := eq53427 (σ x)
       grind)
    | exact resolve eq26 eq53427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53427
  have eq60566 : (M.op (σ x) (σ x)) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq60462 eq722
    | exact resolve eq722 eq60462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq60574 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  have eq60578 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq26462 eq60566
    | exact resolve eq60566 eq26462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60566
  have eq64710 : (M.op x y) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq60578 eq11
    | exact resolve eq11 eq60578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60578
  have eq64726 : (M.op x y) = (k (σ x) (σ x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq64710
  have eq64747 : (M.op x y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have r₁ := eq64726
       have r₂ := eq60574
       grind)
    | exact resolve eq64726 eq60574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60574 eq64726
  have eq65165 : (M.op x y) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ y = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq64747 eq46734
    | exact resolve eq46734 eq64747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46734 eq64747
  have eq65192 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ y = (σ y) ∨ (M.op x y) = (σ y) := by grind
  clear eq65165
  have eq65360 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq23999 eq23999
    | exact resolve eq23999 eq23999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65652 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq23999 x
       grind)
    | (have i₁ := eq18
       have i₂ := eq23999 x
       grind)
    | exact superpose eq23999 eq18
    | (have j1 := eq23999 x
       grind)
    | exact resolve eq18 eq23999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23999
  have eq65755 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq65360 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65360
  have eq65756 : (σ y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq26462 eq65652
    | exact resolve eq65652 eq26462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65652
  have eq65862 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op x y) ∨ (σ y) = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq26476 eq65755
    | (have j0 := eq65755 X0 X1
       have j1 := eq26476 X0 X1
       grind)
    | exact resolve eq65755 eq26476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26476 eq65755
  have eq66028 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq693 X0 x
       have i₂ := eq65756
       grind)
    | exact superpose eq65756 eq693
    | exact resolve eq693 eq65756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71145 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq24100 eq26
    | (have j1 := eq24100 (σ x)
       grind)
    | exact resolve eq26 eq24100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24100
  have eq71168 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24122 eq71145
    | exact resolve eq71145 eq24122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24122 eq71145
  have eq71421 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq71168 eq693
    | exact resolve eq693 eq71168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71430 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq71168 eq11
    | exact resolve eq11 eq71168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71446 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq71430
  have eq71538 : ∀ X0 X1 : G, (k X1 (M.op X0 (σ y))) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq71421 eq751
    | exact resolve eq751 eq71421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq71611 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq71421 eq21242
    | exact resolve eq21242 eq71421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71717 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq71421 eq26
    | (have j1 := eq71421 (σ x)
       grind)
    | exact resolve eq26 eq71421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72061 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq71717 eq738
    | exact resolve eq738 eq71717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72163 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq71717 eq33434
    | exact resolve eq33434 eq71717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72186 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq72163
  have eq74095 : (M.op x y) ≠ (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq74096 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq76917 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq71446 eq98
    | exact resolve eq98 eq71446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71446
  have eq76954 : y = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq76917
    | exact resolve eq76917 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76917
  have eq90239 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) X1) ∨ x = (M.op x y) ∨ (σ y) = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq707 X1 y
       have i₂ := eq65862 X1 X0
       grind)
    | (have i₁ := eq707 X1 y
       have i₂ := eq65862 X0 X1
       grind)
    | exact superpose eq65862 eq707
    | exact resolve eq707 eq65862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90270 : ∀ X0 : G, (σ y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq65862 x X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq65862 X0 x
       grind)
    | exact superpose eq65862 eq18
    | (have j1 := eq65862 x X0
       grind)
    | exact resolve eq18 eq65862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65862
  have eq90475 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 y) X1) ∨ x = (M.op x y) ∨ (σ y) = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq65756 eq90239
    | exact resolve eq90239 eq65756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65756 eq90239
  have eq90599 : ∀ X1 : G, (σ y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) X1) := by
    intro X1
    first
    | exact superpose eq90270 eq90475
    | (have j0 := eq90475 x X1
       grind)
    | exact resolve eq90475 eq90270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90270 eq90475
  have eq90863 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq693 X0 x
       have i₂ := eq90599 X1
       grind)
    | exact superpose eq90599 eq693
    | (have j1 := eq90599 X1
       grind)
    | exact resolve eq693 eq90599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90599
  have eq102504 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq25405 X0 (M.op sF2 sF3)
       grind)
    | exact superpose eq25405 eq26
    | (have j1 := eq25405 (σ x) X0
       grind)
    | exact resolve eq26 eq25405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25405
  have eq102895 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq738 x
       have i₂ := eq102504 (M.op sF0 x)
       grind)
    | exact superpose eq102504 eq738
    | (have j1 := eq102504 X1
       grind)
    | exact resolve eq738 eq102504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq102917 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1022 X0
       have i₂ := eq102504 (M.op sF0 x)
       grind)
    | exact superpose eq102504 eq1022
    | (have j1 := eq102504 X1
       grind)
    | exact resolve eq1022 eq102504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq102972 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq21289
       have i₂ := eq102504 (M.op sF0 x)
       grind)
    | exact superpose eq102504 eq21289
    | (have j1 := eq102504 X0
       grind)
    | exact resolve eq21289 eq102504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102504
  have eq103526 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq102972 eq815
    | (have j0 := eq815 (σ y)
       grind)
    | (have r₁ := eq815 (σ y)
       have r₂ := eq102972 (σ y)
       grind)
    | exact resolve eq815 eq102972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102972
  have eq103626 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq103526
  have eq104172 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq103626 eq693
    | exact resolve eq693 eq103626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103626
  have eq104236 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (τ (σ y)) := by
    intro X0
    first
    | exact superpose eq71421 eq104172
    | (have j0 := eq104172 X0
       have j1 := eq71421 X0
       grind)
    | exact resolve eq104172 eq71421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71421 eq104172
  have eq104256 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 (σ y)) ∨ y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq32 eq104236
    | (have j0 := eq104236 X0
       grind)
    | exact resolve eq104236 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104236
  have eq112789 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have j0 := eq102917 (σ y) (M.op (σ x) (σ y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102917
  have eq112790 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq112789
  have eq112860 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72186 eq112790
    | exact resolve eq112790 eq72186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112864 : (M.op (M.op x y) x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq112790 eq6562
    | (have j0 := eq6562 (M.op (σ x) (σ y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq6562 eq112790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6562 eq112790
  have eq112869 : (M.op (M.op x y) x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq112864
  have eq112874 : (k (σ y) (σ y)) = (M.op (M.op x y) x) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72061 eq112869
    | (have j1 := eq72061 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq112869 eq72061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112869
  have eq112875 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq112860
       have r₂ := eq74096
       grind)
    | exact resolve eq112860 eq74096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112860
  have eq112878 : (σ y) = (M.op (M.op x y) x) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq102895 eq112874
    | (have j1 := eq102895 (M.op (σ x) (σ y)) x
       grind)
    | exact resolve eq112874 eq102895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102895 eq112874
  have eq112879 : (σ y) = (M.op (M.op x y) x) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25457 eq112878
    | exact resolve eq112878 eq25457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112878
  have eq112880 : (σ y) = (M.op (M.op x y) x) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq112879
  have eq112881 : (σ y) = (M.op (M.op x y) x) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72061 eq112880
    | (have j1 := eq72061 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq112880 eq72061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72061 eq112880
  have eq112882 : (σ y) = (M.op (M.op x y) x) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25457 eq112881
    | exact resolve eq112881 eq25457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112881
  have eq112883 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq112882
  have eq114711 : ∀ X0 : G, (M.op X0 (σ y)) = (τ (M.op X0 (σ y))) ∨ y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq104256 eq21289
    | exact resolve eq21289 eq104256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21289 eq104256
  have eq118162 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq112883 eq707
    | exact resolve eq707 eq112883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118172 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq112883 eq118162
    | exact resolve eq118162 eq112883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112883 eq118162
  have eq123093 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq123395 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72186 eq123093
    | (have r₁ := eq123093
       have r₂ := eq72186
       grind)
    | exact resolve eq123093 eq72186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72186 eq123093
  have eq123400 : (σ y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq123395
  have eq123402 : (σ y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq123400
       have r₂ := eq74096
       grind)
    | exact resolve eq123400 eq74096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74096 eq123400
  have eq140075 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq112875 eq815
    | (have j0 := eq815 (σ y)
       grind)
    | (have r₁ := eq815 (σ y)
       have r₂ := eq112875
       grind)
    | exact resolve eq815 eq112875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112875
  have eq140100 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq140075
  have eq140924 : (σ y) = (τ (σ y)) ∨ y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq24143 eq114711
    | exact resolve eq114711 eq24143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24143 eq114711
  have eq141000 : (σ y) = (τ (σ y)) ∨ y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq140924
  have eq141072 : y = (σ y) ∨ y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32 eq141000
    | exact resolve eq141000 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141000
  have eq141073 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq141072
  have eq141142 : ∀ X0 : G, (σ y) ≠ X0 ∨ (σ x) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq141073 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq141073
       grind)
    | exact resolve eq13 eq141073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141155 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq141073 eq11
    | exact resolve eq11 eq141073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141171 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq141155
  have eq143986 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq140100 eq693
    | exact resolve eq693 eq140100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693 eq140100
  have eq144083 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq123402 eq143986
    | exact resolve eq143986 eq123402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123402 eq143986
  have eq146815 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq141171 eq98
    | exact resolve eq98 eq141171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq146852 : y = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq32 eq146815
    | exact resolve eq146815 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146815
  have eq152937 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) x) := by
    intro X0
    grind
  clear eq25457
  have eq160610 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    grind
  clear eq66028
  have eq190658 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq90863 eq26
    | (have j1 := eq90863 (σ x) X0
       grind)
    | exact resolve eq26 eq90863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90863
  have eq190826 : ∀ X0 : G, (σ y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq33434 eq190658
    | (have j0 := eq190658 X0
       have j1 := eq33434 X0
       grind)
    | exact resolve eq190658 eq33434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33434 eq190658
  have eq191215 : ∀ X0 X1 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | exact superpose eq190826 eq703
    | (have j1 := eq190826 X1
       grind)
    | exact resolve eq703 eq190826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703 eq190826
  have eq339289 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ y = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq65192 eq27
    | exact resolve eq27 eq65192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65192
  have eq339493 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ y = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq339289
       have r₂ := eq26848
       grind)
    | exact resolve eq339289 eq26848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339289
  have eq339501 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq339493 eq26
    | exact resolve eq26 eq339493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339493
  have eq340292 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq26733 eq339501
    | exact resolve eq339501 eq26733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26733 eq339501
  have eq341072 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq340292 eq27
    | exact resolve eq27 eq340292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340292
  have eq341255 : y = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq341072
       have r₂ := eq26848
       grind)
    | exact resolve eq341072 eq26848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26848 eq341072
  have eq341271 : (M.op x y) = (M.op x (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq341255
       grind)
    | exact superpose eq341255 eq18
    | exact resolve eq18 eq341255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq341367 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq33532 X0
       have i₂ := eq341255
       grind)
    | exact superpose eq341255 eq33532
    | exact resolve eq33532 eq341255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33532
  have eq341513 : x ≠ (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq341255
  have eq341557 : ∀ X0 : G, (M.op x y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq341367 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341367
  have eq342422 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq341271 eq144083
    | exact resolve eq144083 eq341271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144083
  have eq342431 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq341271 eq160610
    | (have r₁ := eq160610 x
       have r₂ := eq341271
       grind)
    | exact resolve eq160610 eq341271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160610 eq341271
  have eq342535 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = y := by grind
  clear eq342431
  have eq342536 : x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = y := by grind
  clear eq342535
  have eq342538 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq342422
  have eq342627 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (σ y) := by
    first
    | exact superpose eq26462 eq342536
    | exact resolve eq342536 eq26462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26462 eq342536
  have eq342630 : x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq342538
       have r₂ := eq74095
       grind)
    | exact resolve eq342538 eq74095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74095 eq342538
  have eq342748 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (σ y) := by
    first
    | exact superpose eq60462 eq342630
    | exact resolve eq342630 eq60462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60462 eq342630
  have eq346343 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ y) := by
    first
    | exact superpose eq342627 eq21242
    | exact resolve eq21242 eq342627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346346 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ x = (σ y) := by
    first
    | exact superpose eq342627 eq24021
    | exact resolve eq24021 eq342627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24021
  have eq346488 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (σ y) := by grind
  clear eq346346
  have eq346560 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ y) := by
    first
    | exact superpose eq20 eq346343
    | exact resolve eq346343 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346343
  have eq361521 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq341557 eq26
    | (have j1 := eq341557 (σ x)
       grind)
    | exact resolve eq26 eq341557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341557
  have eq361973 : (σ x) = (σ y) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ x = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq361521 eq342748
    | exact resolve eq342748 eq361521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342748
  have eq361974 : (M.op x y) ≠ (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq361521
  have eq361975 : (σ x) = (σ y) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ x = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq361973
  have eq361990 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq361975
       have r₂ := eq361974
       grind)
    | exact resolve eq361975 eq361974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361974 eq361975
  have eq362018 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq361990
       have r₂ := eq341513
       grind)
    | exact resolve eq361990 eq341513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361990
  have eq362044 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq362018 eq32
    | exact resolve eq32 eq362018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq362018
  have eq363257 : x = y ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq30 eq362044
    | exact resolve eq362044 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq362044
  have eq363258 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq363257
  have eq366618 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq363258 eq27
    | exact resolve eq27 eq363258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363258
  have eq366823 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = (σ y) := by
    first
    | exact superpose eq346560 eq366618
    | (have r₁ := eq366618
       have r₂ := eq346560
       grind)
    | exact resolve eq366618 eq346560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346560 eq366618
  have eq366828 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ x = (σ y) := by grind
  clear eq366823
  have eq366829 : x = (M.op x y) ∨ x = y ∨ x = (σ y) := by grind
  clear eq366828
  have eq366831 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq366829
       have r₂ := eq341513
       grind)
    | exact resolve eq366829 eq341513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341513 eq366829
  have eq383955 : ∀ X0 : G, x ≠ y ∨ (k X0 x) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (σ y) := by
    intro X0
    first
    | (have i₁ := eq28 X0 x
       have i₂ := eq346488
       grind)
    | exact superpose eq346488 eq28
    | (have j0 := eq28 X0 x
       grind)
    | exact resolve eq28 eq346488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq383976 : (M.op (M.op x y) x) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (σ y) := by
    first
    | (have i₁ := eq707 x x
       have i₂ := eq346488
       grind)
    | exact superpose eq346488 eq707
    | exact resolve eq707 eq346488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707 eq346488
  have eq384009 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (σ y) := by
    first
    | exact superpose eq366831 eq383976
    | exact resolve eq383976 eq366831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383976
  have eq384027 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (σ y) := by
    intro X0
    first
    | (have j0 := eq383955 X0
       grind)
    | (have r₁ := eq383955 X0
       have r₂ := eq366831
       grind)
    | exact resolve eq383955 eq366831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383955
  have eq384040 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (σ y) := by
    first
    | exact superpose eq366831 eq384009
    | exact resolve eq384009 eq366831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384009
  have eq384041 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (σ y) := by grind
  clear eq384040
  have eq384060 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (σ y) := by
    intro X0
    first
    | exact superpose eq366831 eq384027
    | (have j0 := eq384027 X0
       grind)
    | exact resolve eq384027 eq366831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384027
  have eq384061 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) ∨ x = (σ y) := by
    intro X0
    first
    | (have j0 := eq384060 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384060
  have eq384072 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (σ y) := by
    first
    | exact superpose eq342627 eq384041
    | exact resolve eq384041 eq342627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342627 eq384041
  have eq384134 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (σ y) := by
    first
    | (have i₁ := eq815 x
       have i₂ := eq384061 x
       grind)
    | exact superpose eq384061 eq815
    | (have j0 := eq815 x
       grind)
    | (have r₁ := eq815 x
       have r₂ := eq384061 x
       grind)
    | exact resolve eq815 eq384061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815 eq384061
  have eq384273 : x = (M.op x x) ∨ x = (M.op x y) ∨ x = (σ y) := by grind
  clear eq384134
  have eq384381 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (σ y) := by
    first
    | exact superpose eq384072 eq384273
    | exact resolve eq384273 eq384072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384072 eq384273
  have eq384382 : x = (σ y) ∨ x = (M.op x y) := by grind
  clear eq384381
  have eq384443 : (M.op x y) = (M.op (σ y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq384382
       grind)
    | exact superpose eq384382 eq18
    | exact resolve eq18 eq384382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384598 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26168
       have i₂ := eq384382
       grind)
    | exact superpose eq384382 eq26168
    | exact resolve eq26168 eq384382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26168
  have eq384780 : (M.op x y) ≠ (σ y) ∨ x = (M.op x y) := by grind
  have eq384887 : (σ y) = (M.op (M.op x y) (σ y)) ∨ y = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq384598
       have r₂ := eq384780
       grind)
    | exact resolve eq384598 eq384780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384598
  have eq385007 : (M.op x y) = (M.op (σ y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq366831 eq384443
    | exact resolve eq384443 eq366831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384443
  have eq385052 : (σ y) = (M.op (M.op x y) (σ y)) ∨ x = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq366831 eq384887
    | exact resolve eq384887 eq366831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366831 eq384887
  have eq385142 : (M.op x y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq384382 eq385007
    | exact resolve eq385007 eq384382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385007
  have eq385163 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq384382 eq385052
    | exact resolve eq385052 eq384382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384382 eq385052
  have eq385247 : (M.op x y) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq191215 eq385163
    | (have j1 := eq191215 (σ y) x
       grind)
    | exact resolve eq385163 eq191215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191215 eq385163
  have eq385309 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq385247
       have r₂ := eq384780
       grind)
    | exact resolve eq385247 eq384780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385247
  have eq385351 : (M.op x y) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq385142 eq385309
    | exact resolve eq385309 eq385142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385142 eq385309
  have eq385376 : x = (M.op x y) := by
    first
    | (have r₁ := eq385351
       have r₂ := eq384780
       grind)
    | exact resolve eq385351 eq384780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384780 eq385351
  have eq385388 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq385376
       grind)
    | exact superpose eq385376 eq18
    | exact resolve eq18 eq385376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq385389 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq385376
       grind)
    | exact superpose eq385376 eq22
    | exact resolve eq22 eq385376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq385562 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq71717
       have i₂ := eq385376
       grind)
    | exact superpose eq385376 eq71717
    | exact resolve eq71717 eq385376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71717
  have eq385563 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq76954
       have i₂ := eq385376
       grind)
    | exact superpose eq385376 eq76954
    | exact resolve eq76954 eq385376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76954
  have eq385584 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq118172
       have i₂ := eq385376
       grind)
    | exact superpose eq385376 eq118172
    | exact resolve eq118172 eq385376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118172
  have eq385592 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq146852
       have i₂ := eq385376
       grind)
    | exact superpose eq385376 eq146852
    | exact resolve eq146852 eq385376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146852
  have eq385936 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq385389 eq20
    | exact resolve eq20 eq385389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386831 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq385388 eq8769
    | exact resolve eq8769 eq385388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8769
  have eq386942 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq385388 eq16
    | exact resolve eq16 eq385388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386945 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq385388 eq689
    | exact resolve eq689 eq385388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq386953 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq385388 eq856
    | (have j0 := eq856 (M.op x y) x
       grind)
    | exact resolve eq856 eq385388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq386959 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq386953
  have eq386960 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq386831
  have eq386961 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq386959
       have i₂ := eq385376
       grind)
    | exact superpose eq385376 eq386959
    | exact resolve eq386959 eq385376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386959
  have eq386965 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq21242 eq386960
    | exact resolve eq386960 eq21242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21242 eq386960
  have eq386966 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq386965
       have i₂ := eq385376
       grind)
    | exact superpose eq385376 eq386965
    | exact resolve eq386965 eq385376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386965
  have eq386967 : (k (σ (M.op x y)) (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq385936 eq386966
    | exact resolve eq386966 eq385936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386966
  have eq386968 : (k (σ (M.op x y)) (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq386967
    | exact resolve eq386967 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386967
  have eq386969 : (k (σ x) (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq385936 eq386968
    | exact resolve eq386968 eq385936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386968
  have eq386970 : (k (σ x) (σ x)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq386961 eq386969
    | exact resolve eq386969 eq386961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386961 eq386969
  have eq400704 : (M.op (M.op x y) (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq71168 eq386945
    | exact resolve eq386945 eq71168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71168 eq386945
  have eq401682 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq385562 eq400704
    | exact resolve eq400704 eq385562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385562 eq400704
  have eq417556 : (σ y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq386970 eq141171
    | exact resolve eq141171 eq386970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386970
  have eq417603 : y = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq385592 eq417556
    | exact resolve eq417556 eq385592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385592 eq417556
  have eq417604 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq417603
  have eq432739 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq385584
  have eq474470 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq417604 eq179
    | exact resolve eq179 eq417604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq417604
  have eq474617 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq474470
    | exact resolve eq474470 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474470
  have eq474626 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq385936 eq474617
    | exact resolve eq474617 eq385936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474617
  have eq474633 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have j1 := eq141142 (σ x)
       grind)
    | (have r₁ := eq474626
       have r₂ := eq141142 (σ x)
       grind)
    | (have r₁ := eq474626
       have r₂ := eq141142 y
       grind)
    | exact resolve eq474626 eq141142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141142 eq474626
  have eq474668 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq474633 eq141171
    | exact resolve eq141171 eq474633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141171 eq474633
  have eq474718 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (σ y) := by grind
  clear eq474668
  have eq474777 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq474718 eq27
    | exact resolve eq27 eq474718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474841 : (σ x) = (σ y) ∨ y = (σ y) := by
    first
    | (have r₁ := eq474777
       have r₂ := eq385936
       grind)
    | exact resolve eq474777 eq385936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474777
  have eq475433 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq474841 eq401682
    | exact resolve eq401682 eq474841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401682 eq474841
  have eq475446 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq475433
  have eq475475 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq141073 eq475446
    | exact resolve eq475446 eq141073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141073 eq475446
  have eq475599 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq474718 eq475475
    | exact resolve eq475475 eq474718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474718 eq475475
  have eq475600 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq475599
  have eq475729 : (σ (M.op x y)) ≠ (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq475600 eq27
    | exact resolve eq27 eq475600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475600
  have eq475778 : y = (σ y) := by
    first
    | (have r₁ := eq475729
       have r₂ := eq385936
       grind)
    | exact resolve eq475729 eq385936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475729
  have eq475786 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq24
       have i₂ := eq475778
       grind)
    | exact superpose eq475778 eq24
    | exact resolve eq24 eq475778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq476045 : (M.op x y) = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq385388
       have i₂ := eq475778
       grind)
    | exact superpose eq475778 eq385388
    | exact resolve eq385388 eq475778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385388
  have eq477101 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq476045 eq71538
    | exact resolve eq71538 eq476045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71538
  have eq477103 : (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq476045 eq71611
    | exact resolve eq71611 eq476045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71611
  have eq477142 : (M.op x y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq476045 eq152937
    | exact resolve eq152937 eq476045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152937
  have eq477242 : (σ y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq477142
       have i₂ := eq385376
       grind)
    | exact superpose eq385376 eq477142
    | exact resolve eq477142 eq385376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385376 eq477142
  have eq477248 : (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq477103
    | exact resolve eq477103 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477103
  have eq477258 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq385936 eq477248
    | exact resolve eq477248 eq385936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477248
  have eq486156 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq477258 eq432739
    | (have r₁ := eq432739
       have r₂ := eq477258
       grind)
    | exact resolve eq432739 eq477258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486163 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) := by grind
  have eq486165 : (σ y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) := by grind
  clear eq486156
  have eq486188 : (σ y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) := by
    first
    | (have r₁ := eq486165
       have r₂ := eq486163
       grind)
    | exact resolve eq486165 eq486163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486163 eq486165
  have eq497006 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq477101 eq385563
    | exact resolve eq385563 eq477101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385563 eq477101
  have eq497039 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq497006
  have eq497065 : (M.op x y) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq497039
       have i₂ := eq475778
       grind)
    | exact superpose eq475778 eq497039
    | exact resolve eq497039 eq475778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475778 eq497039
  have eq497172 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq477258 eq497065
    | exact resolve eq497065 eq477258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477258 eq497065
  have eq497173 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by grind
  clear eq497172
  have eq497638 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq497173 eq432739
    | (have r₁ := eq432739
       have r₂ := eq497173
       grind)
    | exact resolve eq432739 eq497173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432739 eq497173
  have eq497653 : (σ y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by grind
  clear eq497638
  have eq497689 : (σ y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq497653
       have r₂ := eq477242
       grind)
    | exact resolve eq497653 eq477242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497653
  have eq497763 : (σ y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq486188 eq497689
    | exact resolve eq497689 eq486188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486188 eq497689
  have eq497815 : (σ y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq497763
       have r₂ := eq477242
       grind)
    | exact resolve eq497763 eq477242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477242 eq497763
  have eq498629 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq497815 eq386942
    | exact resolve eq386942 eq497815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386942 eq497815
  have eq501555 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq498629 eq476045
    | exact resolve eq476045 eq498629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498629
  have eq501976 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq501555 eq27
    | exact resolve eq27 eq501555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501555
  have eq502025 : (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq501976
       have r₂ := eq385936
       grind)
    | exact resolve eq501976 eq385936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385936 eq501976
  have eq502620 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq502025 eq475786
    | exact resolve eq475786 eq502025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475786 eq502025
  have eq506150 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq502620 eq385389
    | exact resolve eq385389 eq502620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385389
  have eq506151 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq502620 eq20
    | exact resolve eq20 eq502620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq502620
  have eq507289 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq506150 eq26
    | exact resolve eq26 eq506150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq506150
  have eq507714 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq476045 eq507289
    | exact resolve eq507289 eq476045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476045 eq507289
  have eq508265 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq507714 eq27
    | exact resolve eq27 eq507714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq507714
  have eq508455 : False := by grind
  exact eq508455
