import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3491`: `x ◇ x = y ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxy_pxx_pxy_Equation3491 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3491 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3491.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq18
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq109 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X0) (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) X0) X2 x
       have i₂ := eq9 X0 (M.op x (M.op (M.op X1 X0) X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq109 X0 x X2
       have i₂ := eq9 X0 (M.op (M.op x X0) X0) x
       grind)
    | (have i₁ := eq109 X0 x X2
       have i₂ := eq9 (M.op (M.op x X0) X0) x X2
       grind)
    | exact superpose eq9 eq109
    | exact resolve eq109 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq113 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq110 (σ X0) x
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq110
    | exact resolve eq110 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (M.op (τ X1) (τ X1)) (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq362 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X1) (σ X1)) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq362 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq362
    | (have j0 := eq362 X0 X1
       grind)
    | exact resolve eq362 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq370 : ∀ X0 X1 : G, (τ X1) = (τ (M.op X1 X1)) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq361 X0 X1
       have i₂ := eq63 X1
       grind)
    | exact superpose eq63 eq361
    | (have j0 := eq361 X0 X1
       grind)
    | exact resolve eq361 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq361
  have eq824 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq369 x y
       grind)
    | exact superpose eq369 eq16
    | (have j1 := eq369 (M.op y y) y
       grind)
    | exact resolve eq16 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq53667 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0)
       have i₂ := eq370 X1 X0
       grind)
    | exact superpose eq370 eq11
    | (have j1 := eq370 X1 X0
       grind)
    | exact resolve eq11 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq53743 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (M.op X0 X0) = X0 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53667 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq53667
    | (have j0 := eq53667 X0 X1
       grind)
    | exact resolve eq53667 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53667
  have eq61814 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53743 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq53743
    | (have j0 := eq53743 (σ X0) X1
       grind)
    | exact resolve eq53743 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53743
  have eq61966 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61814 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq61814
    | (have j0 := eq61814 X0 X1
       grind)
    | exact resolve eq61814 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61814
  have eq61988 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61966 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq61966
    | (have j0 := eq61966 X0 X1
       grind)
    | exact resolve eq61966 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61966
  have eq66438 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq824
       have i₂ := eq61988 y x
       grind)
    | exact superpose eq61988 eq824
    | (have j1 := eq61988 y x
       grind)
    | (have r₁ := eq824
       have r₂ := eq61988 y x
       grind)
    | (have r₁ := eq824
       have r₂ := eq61988 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq824
       have r₂ := eq61988 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq824 eq61988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824 eq61988
  have eq66493 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq66438
  have eq66494 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ x = y := by grind
  clear eq66493
  have eq66829 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq66494
       grind)
    | exact superpose eq66494 eq10
    | exact resolve eq10 eq66494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66494
  have eq66894 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq66829
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq66829
    | exact resolve eq66829 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66829
  have eq66895 : x = y ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq66894
  have eq66897 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66895
       grind)
    | exact superpose eq66895 eq16
    | exact resolve eq16 eq66895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66895
  have eq67015 : (σ y) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq66897
       have r₂ := eq22 x
       grind)
    | exact resolve eq66897 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq66897
  have eq67025 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq113 y x
       have i₂ := eq67015
       grind)
    | exact superpose eq67015 eq113
    | exact resolve eq113 eq67015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq67080 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq67015
       grind)
    | exact superpose eq67015 eq10
    | exact resolve eq10 eq67015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67015
  have eq67179 : y = (M.op y y) := by
    first
    | (have i₁ := eq67080
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq67080
    | exact resolve eq67080 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67080
  have eq67200 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq110 y x
       have i₂ := eq67179
       grind)
    | exact superpose eq67179 eq110
    | exact resolve eq110 eq67179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq67179
  have eq67964 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67025 (σ x)
       grind)
    | exact superpose eq67025 eq16
    | exact resolve eq16 eq67025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67025
  have eq67973 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq67964
       have i₂ := eq67200 x
       grind)
    | exact superpose eq67200 eq67964
    | exact resolve eq67964 eq67200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67200 eq67964
  have eq67974 : False := by grind
  exact eq67974

/-- `Equation3506`: `x ◇ x = y ◇ ((z ◇ w) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyy_pyx_pxy_Equation3506 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3506 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3506.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq176 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op x y) y)) := by
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
  have eq177 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
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
  have eq181 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
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
  have eq197 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq181 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq13
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq181 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq181 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op X2 (M.op (M.op X0 X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 X2 X3 X3
       have i₂ := eq181 X3 X0
       grind)
    | (have i₁ := eq16 X1 X2 X3 X3
       have i₂ := eq181 X0 X3
       grind)
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op x y) y)) ≠ X1 ∨ (k X2 X1) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq176 X0 X1
       grind)
    | (have i₁ := eq13 X0 (M.op (M.op x y) y)
       have i₂ := eq176 X0 (M.op (M.op x y) y)
       grind)
    | exact superpose eq176 eq13
    | (have r₁ := eq13 X0 (M.op X1 (M.op (M.op x y) y))
       have r₂ := eq176 (M.op X1 (M.op (M.op x y) y)) X1
       grind)
    | exact resolve eq13 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X4) X4)) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq16 x X2 X3 X4
       have i₂ := eq176 x X0
       grind)
    | (have i₁ := eq16 (M.op (M.op x y) y) x X2 X3
       have i₂ := eq176 X0 (M.op (M.op x y) y)
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op X2 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0 X2
    first
    | (have i₁ := eq177 x X2
       have i₂ := eq177 x X0
       grind)
    | (have i₁ := eq177 (M.op (M.op (σ x) (σ y)) (σ y)) x
       have i₂ := eq177 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) ≠ X1 ∨ (k X2 X1) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq177 X0 X1
       grind)
    | (have i₁ := eq13 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       have i₂ := eq177 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact superpose eq177 eq13
    | (have r₁ := eq13 X0 (M.op X1 (M.op (M.op (σ x) (σ y)) (σ y)))
       have r₂ := eq177 (M.op X1 (M.op (M.op (σ x) (σ y)) (σ y))) X1
       grind)
    | exact resolve eq13 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X4) X4)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq16 x X2 X3 X4
       have i₂ := eq177 x X0
       grind)
    | (have i₁ := eq16 (M.op (M.op (σ x) (σ y)) (σ y)) x X2 X3
       have i₂ := eq177 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq180 x X2 X3
       have i₂ := eq180 X1 x X0
       grind)
    | (have i₁ := eq180 (M.op X0 X0) X1 X2
       have i₂ := eq180 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq180
    | exact resolve eq180 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) ≠ X2 ∨ (M.op X0 (M.op X1 X1)) = (k X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq180 X0 X1 X2
       grind)
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq180 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq13
    | (have r₁ := eq13 X0 (M.op X2 (M.op X0 X0))
       have r₂ := eq180 X0 (M.op X2 (M.op X0 X0)) X2
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq180 X1 X1 (M.op X1 X1)
       grind)
    | exact resolve eq13 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq421 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq505 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq421 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq421
    | exact resolve eq421 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq695 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X1) X2)) ≠ X3 ∨ (k X4 X3) = (M.op X0 (M.op (M.op X1 X1) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq199 X0 X1 X2 X3
       grind)
    | (have i₁ := eq13 X0 (M.op (M.op X0 X0) X3)
       have i₂ := eq199 X0 X1 (M.op (M.op X0 X0) X3) X3
       grind)
    | exact superpose eq199 eq13
    | (have r₁ := eq13 X0 (M.op X2 (M.op (M.op X0 X0) X3))
       have r₂ := eq199 X0 (M.op X2 (M.op (M.op X0 X0) X3)) X2 X3
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq199 X0 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
       grind)
    | exact resolve eq13 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1033 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X2 X2))) ≠ X3 ∨ (k X4 X3) = (M.op X0 (M.op X1 (M.op X2 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq13 X0 X2
       have i₂ := eq263 X0 X1 X2 X3
       grind)
    | (have i₁ := eq13 X0 (M.op X0 (M.op X1 X1))
       have i₂ := eq263 X0 X1 X2 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq263 eq13
    | (have r₁ := eq13 X0 (M.op X3 (M.op X0 (M.op X1 X1)))
       have r₂ := eq263 X0 X1 (M.op X3 (M.op X0 (M.op X1 X1))) X3
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X1 X1) (M.op X1 X1))
       have r₂ := eq263 (M.op X1 X1) X1 (M.op X1 X1) (M.op (M.op X1 X1) (M.op X1 X1))
       grind)
    | exact resolve eq13 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1645 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1646 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1741 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) y)) ≠ (M.op X0 (M.op (M.op x y) y)) ∨ (M.op X0 (M.op (M.op x y) y)) = X1 ∨ (M.op X0 (M.op (M.op x y) y)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq176 X0 X1
       grind)
    | (have i₁ := eq12 (M.op (M.op x y) y) X1
       have i₂ := eq176 X0 X1
       grind)
    | exact superpose eq176 eq12
    | (have r₁ := eq12 (M.op (M.op x y) y) (M.op (M.op x y) y)
       have r₂ := eq176 (M.op (M.op x y) y) (M.op (M.op x y) y)
       grind)
    | exact resolve eq12 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1742 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) ≠ (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X1 ∨ (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq177 X0 X1
       grind)
    | (have i₁ := eq12 (M.op (M.op (σ x) (σ y)) (σ y)) X1
       have i₂ := eq177 X0 X1
       grind)
    | exact superpose eq177 eq12
    | (have r₁ := eq12 (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq177 (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact resolve eq12 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq1743 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op X0 (M.op X1 X1)) = X2 ∨ (M.op X0 (M.op X1 X1)) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq180 X0 X1 X2
       grind)
    | (have i₁ := eq12 (M.op X0 X0) X2
       have i₂ := eq180 X0 X1 X2
       grind)
    | exact superpose eq180 eq12
    | (have r₁ := eq12 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq180 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq12 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1745 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq181 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq181 X1 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq181 X0 X0
       grind)
    | exact resolve eq12 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq1746 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X2)) ≠ (M.op X0 (M.op (M.op X1 X1) X2)) ∨ (M.op X0 (M.op (M.op X1 X1) X2)) = X3 ∨ (M.op X0 (M.op (M.op X1 X1) X2)) = (k X3 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq199 X0 X1 X2 X3
       grind)
    | (have i₁ := eq12 (M.op (M.op X0 X0) X3) X2
       have i₂ := eq199 X0 X1 X2 X3
       grind)
    | exact superpose eq199 eq12
    | (have r₁ := eq12 (M.op (M.op X0 X0) X3) (M.op (M.op X0 X0) X3)
       have r₂ := eq199 X0 (M.op (M.op X0 X0) X3) (M.op (M.op X0 X0) X3) X3
       grind)
    | exact resolve eq12 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1747 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 X2))) ≠ (M.op X0 (M.op X1 (M.op X2 X2))) ∨ (M.op X0 (M.op X1 (M.op X2 X2))) = X3 ∨ (M.op X0 (M.op X1 (M.op X2 X2))) = (k X3 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X2 X2
       have i₂ := eq263 X0 X1 X2 X3
       grind)
    | (have i₁ := eq12 (M.op X0 (M.op X1 X1)) X3
       have i₂ := eq263 X0 X1 X2 X3
       grind)
    | exact superpose eq263 eq12
    | (have r₁ := eq12 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))
       have r₂ := eq263 X0 X1 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))
       grind)
    | exact resolve eq12 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq1771 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1774 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 X2))) = X3 ∨ (M.op X0 (M.op X1 (M.op X2 X2))) = (k X3 X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1747 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747
  have eq1775 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X2)) = X3 ∨ (M.op X0 (M.op (M.op X1 X1) X2)) = (k X3 X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1746 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1746
  have eq1776 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1745 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1745
  have eq1778 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = X2 ∨ (M.op X0 (M.op X1 X1)) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1743 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743
  have eq1779 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X1 ∨ (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1742 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1742
  have eq1780 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) y)) = X1 ∨ (M.op X0 (M.op (M.op x y) y)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1741 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1741
  have eq1793 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1771 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq1771 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq1771 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1771
  have eq1796 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 X2))) = (k X3 X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1774 X0 X1 X2 (k X3 X3)
       have j1 := eq1033 X0 X1 X2 X3 X3
       grind)
    | (have r₁ := eq1774 X0 X1 X2 X3
       have r₂ := eq1033 X0 X1 X2 X3 x
       grind)
    | (have r₁ := eq1774 X0 X1 X2 (M.op X0 (M.op X1 (M.op X2 X2)))
       have r₂ := eq1033 X0 X1 X2 (M.op X0 (M.op X1 (M.op X2 X2))) x
       grind)
    | (have r₁ := eq1774 X0 X1 X2 X3
       have r₂ := eq1033 X0 X1 X2 (k X3 X3) x
       grind)
    | exact resolve eq1774 eq1033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033 eq1774
  have eq1797 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X1) X2)) = (k X3 X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1775 X0 X1 X2 (k X3 X3)
       have j1 := eq695 X0 X1 X2 X3 X3
       grind)
    | (have r₁ := eq1775 X0 X1 X2 X3
       have r₂ := eq695 X0 X1 X2 X3 x
       grind)
    | (have r₁ := eq1775 X0 X1 X2 (M.op X0 (M.op (M.op X1 X1) X2))
       have r₂ := eq695 X0 X1 X2 (M.op X0 (M.op (M.op X1 X1) X2)) x
       grind)
    | (have r₁ := eq1775 X0 X1 X2 X3
       have r₂ := eq695 X0 X1 X2 (k X3 X3) x
       grind)
    | exact resolve eq1775 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695 eq1775
  have eq1798 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1776 X0 (k X1 X1)
       have j1 := eq197 X0 X1 X1
       grind)
    | (have r₁ := eq1776 X0 X1
       have r₂ := eq197 X0 X1 x
       grind)
    | (have r₁ := eq1776 X0 (M.op X0 X0)
       have r₂ := eq197 X0 (M.op X0 X0) x
       grind)
    | (have r₁ := eq1776 X0 X1
       have r₂ := eq197 X0 (k X1 X1) x
       grind)
    | exact resolve eq1776 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq1776
  have eq1800 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1778 X0 X1 (k X2 X2)
       have j1 := eq280 X0 X1 X2 X2
       grind)
    | (have r₁ := eq1778 X0 X1 X2
       have r₂ := eq280 X0 X1 X2 x
       grind)
    | (have r₁ := eq1778 X0 X1 (M.op X0 (M.op X1 X1))
       have r₂ := eq280 X0 X1 (M.op X0 (M.op X1 X1)) x
       grind)
    | (have r₁ := eq1778 X0 X1 X2
       have r₂ := eq280 X0 X1 (k X2 X2) x
       grind)
    | exact resolve eq1778 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280 eq1778
  have eq1801 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1779 X0 (k X1 X1)
       have j1 := eq241 X0 X1 X1
       grind)
    | (have r₁ := eq1779 X0 X1
       have r₂ := eq241 X0 X1 x
       grind)
    | (have r₁ := eq1779 X0 (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y)))
       have r₂ := eq241 X0 (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) x
       grind)
    | (have r₁ := eq1779 X0 X1
       have r₂ := eq241 X0 (k X1 X1) x
       grind)
    | exact resolve eq1779 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq1779
  have eq1802 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) y)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1780 X0 (k X1 X1)
       have j1 := eq214 X0 X1 X1
       grind)
    | (have r₁ := eq1780 X0 X1
       have r₂ := eq214 X0 X1 x
       grind)
    | (have r₁ := eq1780 X0 (M.op X0 (M.op (M.op x y) y))
       have r₂ := eq214 X0 (M.op X0 (M.op (M.op x y) y)) x
       grind)
    | (have r₁ := eq1780 X0 X1
       have r₂ := eq214 X0 (k X1 X1) x
       grind)
    | exact resolve eq1780 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq1780
  have eq1814 : ∀ X0 X1 X2 X3 : G, (k X3 X3) = (M.op X0 (M.op X1 (k X2 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1796 X0 X1 X2 X3
       have i₂ := eq1793 X2
       grind)
    | exact superpose eq1793 eq1796
    | exact resolve eq1796 eq1793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796
  have eq1815 : ∀ X0 X1 X2 X3 : G, (k X3 X3) = (M.op X0 (M.op (k X1 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1797 X0 X1 X2 X3
       have i₂ := eq1793 X1
       grind)
    | exact superpose eq1793 eq1797
    | exact resolve eq1797 eq1793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1797
  have eq1816 : ∀ X0 X1 X2 : G, (k X2 X2) = (M.op X0 (k X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1800 X0 X1 X2
       have i₂ := eq1793 X1
       grind)
    | exact superpose eq1793 eq1800
    | exact resolve eq1800 eq1793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800
  have eq2004 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq1798 X0 (σ X1)
       grind)
    | exact superpose eq1798 eq10
    | exact resolve eq10 eq1798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2005 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq478 X1 (σ X1)
       have i₂ := eq1798 X0 (σ X1)
       grind)
    | exact superpose eq1798 eq478
    | exact resolve eq478 eq1798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq2006 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq505 X1 X1
       have i₂ := eq1798 X0 (τ X1)
       grind)
    | exact superpose eq1798 eq505
    | exact resolve eq505 eq1798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2007 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X1)
       have i₂ := eq1798 X0 (τ X1)
       grind)
    | exact superpose eq1798 eq34
    | exact resolve eq34 eq1798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1798
  have eq2010 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2007 X0 X1
       have i₂ := eq14 X1
       grind)
    | exact superpose eq14 eq2007
    | exact resolve eq2007 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2007
  have eq2011 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2005 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq2005
    | exact resolve eq2005 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2005
  have eq2034 : ∀ X0 X1 : G, (k X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2010 X0 X1
       have i₂ := eq1793 X0
       grind)
    | exact superpose eq1793 eq2010
    | exact resolve eq2010 eq1793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2010
  have eq2035 : ∀ X0 X1 : G, (k X1 X1) = (τ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2011 X0 X1
       have i₂ := eq1793 X0
       grind)
    | exact superpose eq1793 eq2011
    | exact resolve eq2011 eq1793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2011
  have eq2169 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2004 X1 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq2004
    | exact resolve eq2004 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2232 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) (σ y))) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq224 (M.op sF4 sF3) x
       have i₂ := eq2004 (M.op sF4 sF3) X1
       grind)
    | exact superpose eq2004 eq224
    | exact resolve eq224 eq2004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq2234 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (σ (k X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq199 x X1 X2 (M.op x x)
       have i₂ := eq2004 (M.op x x) X0
       grind)
    | exact superpose eq2004 eq199
    | exact resolve eq199 eq2004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq2331 : ∀ X0 X1 : G, (k X1 X1) = (σ (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2034 x X1
       have i₂ := eq2034 X0 x
       grind)
    | exact superpose eq2034 eq2034
    | exact resolve eq2034 eq2034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2355 : ∀ X0 X1 : G, (τ (k X1 X1)) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq505 X1 X1
       have i₂ := eq2034 X0 (τ X1)
       grind)
    | exact superpose eq2034 eq505
    | exact resolve eq505 eq2034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2434 : ∀ X0 X1 : G, (k X1 X1) = (τ (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2035 x X1
       have i₂ := eq2035 X0 x
       grind)
    | exact superpose eq2035 eq2035
    | exact resolve eq2035 eq2035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2463 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq505 X1 X1
       have i₂ := eq2035 X0 (τ X1)
       grind)
    | exact superpose eq2035 eq505
    | exact resolve eq505 eq2035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2554 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2006 X1 x
       have i₂ := eq2035 X0 x
       grind)
    | exact superpose eq2035 eq2006
    | exact resolve eq2006 eq2035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2035
  have eq2868 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 (M.op (M.op x y) y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2004 X1 x
       have i₂ := eq1802 X0 x
       grind)
    | exact superpose eq1802 eq2004
    | exact resolve eq2004 eq1802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1802
  have eq2925 : ∀ X0 X1 X2 : G, (k X1 X1) = (M.op X2 (σ (k X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1816 X2 x X1
       have i₂ := eq2034 X0 x
       grind)
    | exact superpose eq2034 eq1816
    | exact resolve eq1816 eq2034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3456 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (σ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2169 x X1
       have i₂ := eq2034 X0 x
       grind)
    | exact superpose eq2034 eq2169
    | exact resolve eq2169 eq2034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2169
  have eq3626 : ∀ X0 X1 : G, (k X1 X1) = (σ (σ (σ (σ (k X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2331 x X1
       have i₂ := eq2331 X0 x
       grind)
    | exact superpose eq2331 eq2331
    | exact resolve eq2331 eq2331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3656 : ∀ X0 X1 : G, (k X1 X1) = (σ (σ (σ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2034 x X1
       have i₂ := eq2331 X0 x
       grind)
    | exact superpose eq2331 eq2034
    | exact resolve eq2034 eq2331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2034
  have eq3753 : ∀ X0 X1 : G, (τ (k X1 X1)) = (σ (σ (σ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2355 x X1
       have i₂ := eq2331 X0 x
       grind)
    | exact superpose eq2331 eq2355
    | exact resolve eq2355 eq2331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3906 : ∀ X0 X2 X3 : G, (M.op X2 (k X3 X3)) = (τ (τ (k X0 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1816 X2 X3 x
       have i₂ := eq2434 X0 x
       grind)
    | exact superpose eq2434 eq1816
    | exact resolve eq1816 eq2434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3912 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (τ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2006 X1 x
       have i₂ := eq2434 X0 x
       grind)
    | exact superpose eq2434 eq2006
    | exact resolve eq2006 eq2434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2006
  have eq3922 : ∀ X0 X2 : G, (σ (k X2 X2)) = (τ (τ (τ (k X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq2355 X2 x
       have i₂ := eq2434 X0 x
       grind)
    | exact superpose eq2434 eq2355
    | exact resolve eq2355 eq2434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3931 : ∀ X0 X1 : G, (τ (k X1 X1)) = (τ (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq505 X1 X1
       have i₂ := eq2434 X0 (τ X1)
       grind)
    | exact superpose eq2434 eq505
    | exact resolve eq505 eq2434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq4779 : ∀ X0 X1 X2 : G, (σ (k X2 X2)) = (M.op X0 (σ (k X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2232 X0 (M.op sF4 sF3)
       have i₂ := eq2234 X0 (M.op sF4 sF3) X2
       grind)
    | exact superpose eq2234 eq2232
    | exact resolve eq2232 eq2234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2232 eq2234
  have eq6681 : ∀ X0 X1 X2 X3 : G, (k X2 X2) = (M.op X3 (M.op X0 (σ (k X1 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1816 X3 x X2
       have i₂ := eq2925 X1 x X0
       grind)
    | exact superpose eq2925 eq1816
    | exact resolve eq1816 eq2925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1816 eq2925
  have eq9439 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (σ (σ (σ (k X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3456 x X1
       have i₂ := eq2331 X0 x
       grind)
    | exact superpose eq2331 eq3456
    | exact resolve eq3456 eq2331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3456
  have eq9921 : ∀ X0 X1 : G, (k X1 X1) = (σ (σ (σ (σ (σ (k X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2331 x X1
       have i₂ := eq3656 X0 x
       grind)
    | exact superpose eq3656 eq2331
    | exact resolve eq2331 eq3656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2331 eq3656
  have eq10363 : ∀ X0 X2 : G, (τ (τ (k X2 X2))) = (τ (τ (τ (k X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq2554 X2 x
       have i₂ := eq3912 X0 x
       grind)
    | exact superpose eq3912 eq2554
    | exact resolve eq2554 eq3912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2554
  have eq12269 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op X0 (M.op (k X1 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1801 X3 x
       have i₂ := eq1815 X0 X1 X2 x
       grind)
    | exact superpose eq1815 eq1801
    | exact resolve eq1801 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1801 eq1815
  have eq15686 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1645
       grind)
    | exact superpose eq1645 eq40
    | exact resolve eq40 eq1645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645
  have eq15687 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq15686
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15686
    | exact resolve eq15686 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15686
  have eq15689 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq15687
    | exact resolve eq15687 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15687
  have eq15691 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq15689
       have i₂ := eq1793 y
       grind)
    | exact superpose eq1793 eq15689
    | exact resolve eq15689 eq1793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15689
  have eq439620 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq15691 eq1646
    | exact resolve eq1646 eq15691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq439629 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq439620
       have r₂ := eq27
       grind)
    | exact resolve eq439620 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439620
  have eq439636 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq439629
       have i₂ := eq1793 sF3
       grind)
    | exact superpose eq1793 eq439629
    | exact resolve eq439629 eq1793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439629
  have eq439642 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq439636 eq12
    | (have j0 := eq12 x (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq439636
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq439636
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq439636
       grind)
    | exact resolve eq12 eq439636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439636
  have eq439690 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq439642
       have r₂ := eq26
       grind)
    | exact resolve eq439642 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439642
  have eq439698 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq439690
       have i₂ := eq1793 sF3
       grind)
    | exact superpose eq1793 eq439690
    | exact resolve eq439690 eq1793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439690
  have eq439699 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq439698
  have eq439703 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq15691 eq439699
    | exact resolve eq439699 eq15691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15691 eq439699
  have eq439705 : (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq439703
       have r₂ := eq27
       grind)
    | exact resolve eq439703 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439703
  have eq439712 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq439705 eq152
    | exact resolve eq152 eq439705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439705
  have eq440223 : y = (k y y) ∨ y = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq31 eq439712
    | exact resolve eq439712 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439712
  have eq440224 : (M.op x y) = (M.op y x) ∨ y = (k y y) := by grind
  clear eq440223
  have eq440348 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y y) ∨ (M.op x y) = (k x y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq440224
       grind)
    | exact superpose eq440224 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq440224
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq440224
       grind)
    | exact resolve eq12 eq440224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440224
  have eq440396 : y = (M.op y y) ∨ (M.op x y) = (k x y) ∨ y = (k y y) := by
    first
    | (have r₁ := eq440348
       have r₂ := eq18
       grind)
    | exact resolve eq440348 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440348
  have eq440404 : y = (k y y) ∨ (M.op x y) = (k x y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq440396
       have i₂ := eq1793 y
       grind)
    | exact superpose eq1793 eq440396
    | exact resolve eq440396 eq1793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440396
  have eq440405 : (M.op x y) = (k x y) ∨ y = (k y y) := by grind
  clear eq440404
  have eq440413 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq440405
       grind)
    | exact superpose eq440405 eq40
    | exact resolve eq40 eq440405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq440405
  have eq440415 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq440413
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq440413
    | exact resolve eq440413 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq440413
  have eq440419 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq20 eq440415
    | exact resolve eq440415 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440415
  have eq440424 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq440419 eq1646
    | exact resolve eq1646 eq440419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq440433 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq440424
       have r₂ := eq27
       grind)
    | exact resolve eq440424 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440424
  have eq440440 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq440433
       have i₂ := eq1793 sF3
       grind)
    | exact superpose eq1793 eq440433
    | exact resolve eq440433 eq1793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440433
  have eq460692 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq440440 eq12
    | (have j0 := eq12 x (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq440440
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq440440
       grind)
    | exact resolve eq12 eq440440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440440
  have eq460740 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq460692
       have r₂ := eq26
       grind)
    | exact resolve eq460692 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460692
  have eq460748 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq460740
       have i₂ := eq1793 sF3
       grind)
    | exact superpose eq1793 eq460740
    | exact resolve eq460740 eq1793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1793 eq460740
  have eq460749 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (k y y) := by grind
  clear eq460748
  have eq460753 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq440419 eq460749
    | exact resolve eq460749 eq440419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440419 eq460749
  have eq460755 : (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq460753
       have r₂ := eq27
       grind)
    | exact resolve eq460753 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460753
  have eq460763 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (k y y) := by
    first
    | exact superpose eq460755 eq152
    | exact resolve eq152 eq460755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq460755
  have eq461301 : y = (k y y) ∨ y = (k y y) := by
    first
    | exact superpose eq31 eq460763
    | exact resolve eq460763 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460763
  have eq461302 : y = (k y y) := by grind
  clear eq461301
  have eq461430 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op X1 (M.op X2 y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1814 X1 X2 y X0
       have i₂ := eq461302
       grind)
    | exact superpose eq461302 eq1814
    | exact resolve eq1814 eq461302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814
  have eq461446 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq2004 X0 y
       have i₂ := eq461302
       grind)
    | exact superpose eq461302 eq2004
    | exact resolve eq2004 eq461302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2004
  have eq461470 : ∀ X0 : G, (σ y) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2355 y X0
       have i₂ := eq461302
       grind)
    | exact superpose eq461302 eq2355
    | exact resolve eq2355 eq461302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2355
  have eq461471 : ∀ X0 : G, (k X0 X0) = (τ (τ y)) := by
    intro X0
    first
    | (have i₁ := eq2434 y X0
       have i₂ := eq461302
       grind)
    | exact superpose eq461302 eq2434
    | exact resolve eq2434 eq461302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2434
  have eq461473 : ∀ X0 : G, (τ (k X0 X0)) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq2463 y X0
       have i₂ := eq461302
       grind)
    | exact superpose eq461302 eq2463
    | exact resolve eq2463 eq461302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2463
  have eq461536 : ∀ X0 : G, (k X0 X0) = (σ (σ (σ (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq3626 y X0
       have i₂ := eq461302
       grind)
    | exact superpose eq461302 eq3626
    | exact resolve eq3626 eq461302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3626
  have eq461544 : ∀ X0 : G, (τ (k X0 X0)) = (σ (σ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq3753 y X0
       have i₂ := eq461302
       grind)
    | exact superpose eq461302 eq3753
    | exact resolve eq3753 eq461302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3753
  have eq461553 : ∀ X0 X1 : G, (τ (τ (k X1 X1))) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq3906 X1 X0 y
       have i₂ := eq461302
       grind)
    | exact superpose eq461302 eq3906
    | exact resolve eq3906 eq461302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3906
  have eq461555 : ∀ X0 : G, (M.op X0 X0) = (τ (τ (τ y))) := by
    intro X0
    first
    | (have i₁ := eq3912 y X0
       have i₂ := eq461302
       grind)
    | exact superpose eq461302 eq3912
    | exact resolve eq3912 eq461302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3912
  have eq461558 : ∀ X0 : G, (σ (k X0 X0)) = (τ (τ (τ y))) := by
    intro X0
    first
    | (have i₁ := eq3922 y X0
       have i₂ := eq461302
       grind)
    | exact superpose eq461302 eq3922
    | exact resolve eq3922 eq461302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3922
  have eq461559 : ∀ X0 : G, (τ (k X0 X0)) = (τ (τ y)) := by
    intro X0
    first
    | (have i₁ := eq3931 y X0
       have i₂ := eq461302
       grind)
    | exact superpose eq461302 eq3931
    | exact resolve eq3931 eq461302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3931
  have eq461579 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq4779 X1 y X0
       have i₂ := eq461302
       grind)
    | exact superpose eq461302 eq4779
    | exact resolve eq4779 eq461302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4779
  have eq461611 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op X1 (M.op X2 (σ y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6681 X2 y X0 X1
       have i₂ := eq461302
       grind)
    | exact superpose eq461302 eq6681
    | exact resolve eq6681 eq461302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6681
  have eq461718 : ∀ X0 : G, (M.op X0 X0) = (σ (σ (σ (σ (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq9439 y X0
       have i₂ := eq461302
       grind)
    | exact superpose eq461302 eq9439
    | exact resolve eq9439 eq461302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9439
  have eq461722 : ∀ X0 : G, (k X0 X0) = (σ (σ (σ (σ (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq9921 y X0
       have i₂ := eq461302
       grind)
    | exact superpose eq461302 eq9921
    | exact resolve eq9921 eq461302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9921
  have eq461725 : ∀ X0 : G, (τ (τ (k X0 X0))) = (τ (τ (τ y))) := by
    intro X0
    first
    | (have i₁ := eq10363 y X0
       have i₂ := eq461302
       grind)
    | exact superpose eq461302 eq10363
    | exact resolve eq10363 eq461302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10363 eq461302
  have eq461797 : ∀ X0 : G, (k X0 X0) = (σ (σ (σ (σ (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq461722 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq461722
    | (have j0 := eq461722 X0
       grind)
    | exact resolve eq461722 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461722
  have eq461801 : ∀ X0 : G, (M.op X0 X0) = (σ (σ (σ (σ (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq461718 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq461718
    | (have j0 := eq461718 X0
       grind)
    | exact resolve eq461718 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461718
  have eq461849 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op X1 (M.op X2 (σ y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq461611 X0 X1 X2
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq461611
    | (have j0 := eq461611 X0 X1 X2
       grind)
    | exact resolve eq461611 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461611
  have eq461864 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq461579 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq461579
    | (have j0 := eq461579 X0 X1
       grind)
    | exact resolve eq461579 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461579
  have eq461876 : ∀ X0 : G, (τ (τ (τ y))) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq461553 X0 x
       have i₂ := eq461725 x
       grind)
    | exact superpose eq461725 eq461553
    | exact resolve eq461553 eq461725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461553 eq461725
  have eq461882 : ∀ X0 : G, (τ (k X0 X0)) = (σ (σ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq461544 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq461544
    | (have j0 := eq461544 X0
       grind)
    | exact resolve eq461544 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461544
  have eq461889 : ∀ X0 : G, (k X0 X0) = (σ (σ (σ (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq461536 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq461536
    | (have j0 := eq461536 X0
       grind)
    | exact resolve eq461536 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461536
  have eq461924 : (σ y) = (τ y) := by
    first
    | (have i₁ := eq461470 x
       have i₂ := eq461473 x
       grind)
    | exact superpose eq461473 eq461470
    | exact resolve eq461470 eq461473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461470 eq461473
  have eq461946 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq461446 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq461446
    | (have j0 := eq461446 X0
       grind)
    | exact resolve eq461446 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461446
  have eq461954 : ∀ X1 X2 : G, (τ (τ y)) = (M.op X1 (M.op X2 y)) := by
    intro X1 X2
    first
    | (have i₁ := eq461430 x X1 X2
       have i₂ := eq461471 x
       grind)
    | exact superpose eq461471 eq461430
    | exact resolve eq461430 eq461471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461430
  have eq461964 : (σ (σ (σ (σ (σ y))))) = (τ (τ y)) := by
    first
    | (have i₁ := eq461797 x
       have i₂ := eq461471 x
       grind)
    | exact superpose eq461471 eq461797
    | exact resolve eq461797 eq461471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461797
  have eq461967 : (σ (σ (σ (σ (σ y))))) = (τ (τ (τ y))) := by
    first
    | (have i₁ := eq461801 x
       have i₂ := eq461555 x
       grind)
    | exact superpose eq461555 eq461801
    | exact resolve eq461801 eq461555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461555 eq461801
  have eq462001 : ∀ X1 X2 : G, (M.op X1 (M.op X2 (σ y))) = (τ (τ y)) := by
    intro X1 X2
    first
    | (have i₁ := eq461849 x X1 X2
       have i₂ := eq461471 x
       grind)
    | exact superpose eq461471 eq461849
    | exact resolve eq461849 eq461471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461849
  have eq462013 : ∀ X1 : G, (M.op X1 (σ y)) = (τ (τ (τ y))) := by
    intro X1
    first
    | (have i₁ := eq461864 x X1
       have i₂ := eq461558 x
       grind)
    | exact superpose eq461558 eq461864
    | exact resolve eq461864 eq461558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461558 eq461864
  have eq462021 : (σ (σ (σ y))) = (τ (τ y)) := by
    first
    | (have i₁ := eq461882 x
       have i₂ := eq461559 x
       grind)
    | exact superpose eq461559 eq461882
    | exact resolve eq461882 eq461559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461559 eq461882
  have eq462027 : (σ (σ (σ (σ y)))) = (τ (τ y)) := by
    first
    | (have i₁ := eq461889 x
       have i₂ := eq461471 x
       grind)
    | exact superpose eq461471 eq461889
    | exact resolve eq461889 eq461471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461889
  have eq462055 : (σ y) = (τ y) := by
    first
    | (have i₁ := eq461924
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq461924
    | exact resolve eq461924 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq461924
  have eq462074 : ∀ X1 : G, (τ (τ y)) = (M.op X1 (τ (τ (τ y)))) := by
    intro X1
    first
    | (have i₁ := eq461954 X1 x
       have i₂ := eq461876 x
       grind)
    | exact superpose eq461876 eq461954
    | exact resolve eq461954 eq461876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461876 eq461954
  have eq462078 : (τ (τ y)) = (τ (τ (τ y))) := by
    first
    | exact superpose eq461964 eq461967
    | exact resolve eq461967 eq461964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461964 eq461967
  have eq462105 : (τ (τ y)) = (σ (τ (τ y))) := by
    first
    | exact superpose eq462021 eq462027
    | exact resolve eq462027 eq462021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462021 eq462027
  have eq462128 : ∀ X1 : G, (τ (σ y)) = (M.op X1 (τ (τ (σ y)))) := by
    intro X1
    first
    | (have i₁ := eq462074 X1
       have i₂ := eq462055
       grind)
    | exact superpose eq462055 eq462074
    | exact resolve eq462074 eq462055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462074
  have eq462130 : (τ (σ y)) = (τ (τ (σ y))) := by
    first
    | (have i₁ := eq462078
       have i₂ := eq462055
       grind)
    | exact superpose eq462055 eq462078
    | exact resolve eq462078 eq462055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462078
  have eq462144 : (τ y) = (τ (τ y)) := by
    first
    | (have i₁ := eq462105
       have i₂ := eq14 (τ y)
       grind)
    | exact superpose eq14 eq462105
    | exact resolve eq462105 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462105
  have eq462155 : ∀ X1 : G, y = (M.op X1 (τ y)) := by
    intro X1
    first
    | exact superpose eq31 eq462128
    | exact resolve eq462128 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462128
  have eq462157 : y = (τ y) := by
    first
    | exact superpose eq31 eq462130
    | exact resolve eq462130 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462130
  have eq462167 : (σ y) = (τ (σ y)) := by
    first
    | (have i₁ := eq462144
       have i₂ := eq462055
       grind)
    | exact superpose eq462055 eq462144
    | exact resolve eq462144 eq462055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462144
  have eq462177 : ∀ X1 : G, y = (M.op X1 (σ y)) := by
    intro X1
    first
    | (have i₁ := eq462155 X1
       have i₂ := eq462055
       grind)
    | exact superpose eq462055 eq462155
    | exact resolve eq462155 eq462055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462155
  have eq462179 : y = (σ y) := by
    first
    | (have i₁ := eq462157
       have i₂ := eq462055
       grind)
    | exact superpose eq462055 eq462157
    | exact resolve eq462157 eq462055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462157
  have eq462203 : (M.op x y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq462179
       grind)
    | exact superpose eq462179 eq18
    | exact resolve eq18 eq462179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq462210 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X2)) = (M.op X3 (M.op (M.op x y) (σ y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq215 X3 X0 X1 X2
       have i₂ := eq462179
       grind)
    | exact superpose eq462179 eq215
    | exact resolve eq215 eq462179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq462485 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) X2)) = (τ (τ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq462001 eq462210
    | exact resolve eq462210 eq462001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462001 eq462210
  have eq462490 : (M.op x y) = (τ (τ (τ y))) := by
    first
    | exact superpose eq462013 eq462203
    | exact resolve eq462203 eq462013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462013 eq462203
  have eq462566 : ∀ X0 X1 X2 : G, (τ (σ y)) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq462485 X0 X1 X2
       have i₂ := eq462055
       grind)
    | exact superpose eq462055 eq462485
    | exact resolve eq462485 eq462055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462485
  have eq462569 : (M.op x y) = (τ (τ (σ y))) := by
    first
    | (have i₁ := eq462490
       have i₂ := eq462055
       grind)
    | exact superpose eq462055 eq462490
    | exact resolve eq462490 eq462055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462490
  have eq462633 : ∀ X0 X1 X2 : G, y = (M.op X0 (M.op (M.op X1 X2) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq31 eq462566
    | exact resolve eq462566 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462566
  have eq462636 : (M.op x y) = (τ y) := by
    first
    | exact superpose eq31 eq462569
    | exact resolve eq462569 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462569
  have eq462691 : ∀ X0 X1 X2 : G, (σ y) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq462633 X0 X1 X2
       have i₂ := eq462179
       grind)
    | exact superpose eq462179 eq462633
    | exact resolve eq462633 eq462179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462633
  have eq462693 : (M.op x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq462636
       have i₂ := eq462179
       grind)
    | exact superpose eq462179 eq462636
    | exact resolve eq462636 eq462179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462636
  have eq463214 : (M.op x y) = (σ y) := by
    first
    | exact superpose eq462693 eq462167
    | exact resolve eq462167 eq462693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462167
  have eq463215 : y = (M.op x y) := by
    first
    | exact superpose eq462693 eq31
    | exact resolve eq31 eq462693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462693
  have eq463282 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X2)) = (M.op X3 (M.op (M.op (σ x) (σ y)) (M.op x y))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq463214 eq242
    | exact resolve eq242 eq463214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq463398 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (k X2 X2) X3)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op x y))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq463214 eq12269
    | exact resolve eq12269 eq463214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12269
  have eq463461 : ∀ X0 X1 X3 : G, (M.op X1 (M.op (τ (τ y)) X3)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op x y))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq463398 X0 X1 x X3
       have i₂ := eq461471 x
       grind)
    | exact superpose eq461471 eq463398
    | exact resolve eq463398 eq461471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461471 eq463398
  have eq463566 : ∀ X3 : G, (σ y) = (M.op X3 (M.op (M.op (σ x) (σ y)) (M.op x y))) := by
    intro X3
    first
    | (have i₁ := eq463282 x x x X3
       have i₂ := eq462691 x x x
       grind)
    | exact superpose eq462691 eq463282
    | exact resolve eq463282 eq462691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462691 eq463282
  have eq463619 : ∀ X0 X1 X3 : G, (M.op X1 (M.op (τ (σ y)) X3)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op x y))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq463461 X0 X1 X3
       have i₂ := eq462055
       grind)
    | exact superpose eq462055 eq463461
    | exact resolve eq463461 eq462055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462055 eq463461
  have eq463724 : ∀ X3 : G, (M.op x y) = (M.op X3 (M.op (M.op (σ x) (σ y)) (M.op x y))) := by
    intro X3
    first
    | exact superpose eq463214 eq463566
    | exact resolve eq463566 eq463214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463566
  have eq463769 : ∀ X0 X1 X3 : G, (M.op X1 (M.op y X3)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op x y))) := by
    intro X0 X1 X3
    first
    | exact superpose eq31 eq463619
    | exact resolve eq463619 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq463619
  have eq463909 : ∀ X1 X3 : G, (M.op x y) = (M.op X1 (M.op y X3)) := by
    intro X1 X3
    first
    | exact superpose eq463724 eq463769
    | exact resolve eq463769 eq463724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463724 eq463769
  have eq464040 : ∀ X1 X3 : G, (M.op x y) = (M.op X1 (M.op (σ y) X3)) := by
    intro X1 X3
    first
    | (have i₁ := eq463909 X1 X3
       have i₂ := eq462179
       grind)
    | exact superpose eq462179 eq463909
    | exact resolve eq463909 eq462179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463909
  have eq464150 : ∀ X1 X3 : G, (M.op x y) = (M.op X1 (M.op (M.op x y) X3)) := by
    intro X1 X3
    first
    | exact superpose eq463214 eq464040
    | exact resolve eq464040 eq463214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464040
  have eq464359 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 (M.op (M.op x y) (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2868 X1 X0
       have i₂ := eq463215
       grind)
    | exact superpose eq463215 eq2868
    | exact resolve eq2868 eq463215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2868 eq463215
  have eq464573 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq464150 eq464359
    | exact resolve eq464359 eq464150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464150 eq464359
  have eq464677 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq464573
    | (have j0 := eq464573 X0
       grind)
    | exact resolve eq464573 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq464573
  have eq464767 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq464677 x
       have i₂ := eq461946 x
       grind)
    | exact superpose eq461946 eq464677
    | exact resolve eq464677 eq461946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461946 eq464677
  have eq464828 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq463214 eq464767
    | exact resolve eq464767 eq463214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464767
  have eq485823 : y = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq462177 eq26
    | (have j1 := eq462177 (σ x)
       grind)
    | exact resolve eq26 eq462177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq462177
  have eq486000 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq485823
       have i₂ := eq462179
       grind)
    | exact superpose eq462179 eq485823
    | exact resolve eq485823 eq462179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462179 eq485823
  have eq486140 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq463214 eq486000
    | exact resolve eq486000 eq463214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463214 eq486000
  have eq486574 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq486140 eq27
    | exact resolve eq27 eq486140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq486140
  have eq486798 : False := by grind
  exact eq486798

/-- `Equation3506`: `x ◇ x = y ◇ ((z ◇ w) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation3506 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3506 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3506.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
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
  clear eq44
  have eq89 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq93 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq89 sF2
       grind)
    | exact superpose eq89 eq50
    | exact resolve eq50 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq94 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq93
       have i₂ := eq89 x
       grind)
    | exact superpose eq89 eq93
    | exact resolve eq93 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq93
  have eq107 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq45
       have i₂ := eq107 x y
       grind)
    | exact superpose eq107 eq45
    | (have j1 := eq107 (σ (M.op x y)) (k (σ x) (σ y))
       grind)
    | exact resolve eq45 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq126 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq121
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq121
    | exact resolve eq121 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq127 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq126
    | exact resolve eq126 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq130 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq127 eq107
    | (have j0 := eq107 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq107 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq127
  have eq131 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq130
    | exact resolve eq130 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq134 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq131
       have r₂ := eq28
       grind)
    | exact resolve eq131 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq139 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq134 eq30
    | exact resolve eq30 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq134
  have eq141 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq139
    | exact resolve eq139 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq139
  have eq142 : x = y := by grind
  clear eq141
  have eq147 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq142
       grind)
    | exact superpose eq142 eq19
    | exact resolve eq19 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq148 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq142
       grind)
    | exact superpose eq142 eq25
    | exact resolve eq25 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq142
  have eq149 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq148
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq148
    | exact resolve eq148 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq148
  have eq155 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq149 eq27
    | exact resolve eq27 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq149
  have eq171 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq155 eq94
    | exact resolve eq94 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq155
  have eq177 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq171
       have i₂ := eq147
       grind)
    | exact superpose eq147 eq171
    | exact resolve eq171 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq171
  have eq183 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq177 eq15
    | exact resolve eq15 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq184 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq183
    | exact resolve eq183 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq183
  have eq185 : False := by grind
  exact eq185

/-- `Equation3506`: `x ◇ x = y ◇ ((z ◇ w) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation3506 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3506 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3506.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X3) X3)) := by
    intro X0 X1 X2 X3
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x x x
       have i₂ := eq14 X1 x x x
       grind)
    | (have i₁ := eq14 X0 (M.op (M.op x x) x) x x
       have i₂ := eq14 (M.op (M.op x x) x) X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : x ≠ (M.op x y) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq104
    | exact resolve eq104 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq116 : ∀ X0 : G, (M.op x x) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq92
       have i₂ := eq60 sF2 x
       grind)
    | (have i₁ := eq92
       have i₂ := eq60 X0 sF2
       grind)
    | exact superpose eq60 eq92
    | exact resolve eq92 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq92
  have eq2684 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq107 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2685 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq2684
    | exact resolve eq2684 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2684
  have eq2688 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq2685
       have r₂ := eq28
       grind)
    | exact resolve eq2685 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2685
  have eq2690 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq2688
    | exact resolve eq2688 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2688
  have eq2890 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2690 eq28
    | exact resolve eq28 eq2690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2892 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2690 eq85
    | (have r₁ := eq85
       have r₂ := eq2690
       grind)
    | exact resolve eq85 eq2690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq2690
  have eq2899 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2892
  have eq2900 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2899
  have eq2910 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2900 eq107
    | exact resolve eq107 eq2900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq2900
  have eq2914 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2910
  have eq2919 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2914
       have r₂ := eq2890
       grind)
    | exact resolve eq2914 eq2890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2890 eq2914
  have eq2924 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2919 eq30
    | exact resolve eq30 eq2919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2919
  have eq2947 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq2924
    | exact resolve eq2924 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2924
  have eq2948 : x = (M.op x y) ∨ x = y := by grind
  clear eq2947
  have eq2951 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2948 eq21
    | exact resolve eq21 eq2948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2954 : x ≠ x ∨ x = y ∨ x = (k x y) ∨ x = y := by
    first
    | exact superpose eq2948 eq84
    | (have r₁ := eq84
       have r₂ := eq2948
       grind)
    | exact resolve eq84 eq2948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq2948
  have eq2968 : x ≠ x ∨ x = y ∨ x = (k x y) := by grind
  clear eq2954
  have eq2969 : x = (k x y) ∨ x = y := by grind
  clear eq2968
  have eq2985 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq2951
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2951
    | exact resolve eq2951 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2951
  have eq3240 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq2969
       grind)
    | exact superpose eq2969 eq49
    | exact resolve eq49 eq2969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq2969
  have eq3245 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq3240
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3240
    | exact resolve eq3240 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3240
  have eq3262 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3245 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq3245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3245
  have eq3263 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3262
  have eq3269 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq3263
    | exact resolve eq3263 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3263
  have eq3508 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3269 eq28
    | exact resolve eq28 eq3269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3269
  have eq3528 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq3508
       have r₂ := eq2985
       grind)
    | exact resolve eq3508 eq2985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2985 eq3508
  have eq3530 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq3528 eq30
    | exact resolve eq30 eq3528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3528
  have eq3560 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq3530
    | exact resolve eq3530 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3530
  have eq3561 : x = y := by grind
  clear eq3560
  have eq3564 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq3561
       grind)
    | exact superpose eq3561 eq19
    | exact resolve eq19 eq3561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3565 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq3561
       grind)
    | exact superpose eq3561 eq25
    | exact resolve eq25 eq3561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq3561
  have eq3589 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3565
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3565
    | exact resolve eq3565 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3565
  have eq3592 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3589 eq27
    | exact resolve eq27 eq3589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3589
  have eq3710 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3592 eq116
    | exact resolve eq116 eq3592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq3592
  have eq3730 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3710
       have i₂ := eq3564
       grind)
    | exact superpose eq3564 eq3710
    | exact resolve eq3710 eq3564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3564 eq3710
  have eq4031 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3730 eq15
    | exact resolve eq15 eq3730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3730
  have eq4054 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq4031
    | exact resolve eq4031 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq4031
  have eq4064 : False := by grind
  exact eq4064

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pxy_pxy_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq22 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq22 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq27 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq34 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq30 X1 (k X1 X1)
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq30 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq30 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq32 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq32 X1 (k X1 X1)
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq32 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq32 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq39 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq34 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq36
    | (have j0 := eq36 X0 X1
       grind)
    | exact resolve eq36 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq37
    | (have j0 := eq37 X0 X1
       grind)
    | exact resolve eq37 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq37
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq41 X0 X1
       grind)
    | (have r₁ := eq42 X0 X1
       have r₂ := eq41 X0 X1
       grind)
    | exact resolve eq42 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq42
  have eq111 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq115 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq111 X0 X1
       have j1 := eq44 X0 X1
       grind)
    | (have r₁ := eq111 X0 X1
       have r₂ := eq44 X0 X1
       grind)
    | (have r₁ := eq111 X1 X1
       have r₂ := eq44 X1 X1
       grind)
    | exact resolve eq111 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq111
  have eq217 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq115 (σ X0) (σ X1)
       grind)
    | exact superpose eq115 eq15
    | exact resolve eq15 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq217 X0 X1
       have i₂ := eq115 X0 X1
       grind)
    | exact superpose eq115 eq217
    | exact resolve eq217 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq217
  have eq225 : False := by grind
  exact eq225

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq86 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq202 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq86 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq86 X0 X1
       grind)
    | exact superpose eq86 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq86 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq86 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq86 X0 X1
       grind)
    | exact resolve eq13 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq214 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq202 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq215 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq214 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq223 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq215 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq215
    | (have j0 := eq215 X0 X1
       grind)
    | exact resolve eq215 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq224 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq223 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq562 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq224 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq224
    | exact resolve eq224 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq576 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq224 x y
       grind)
    | exact superpose eq224 eq16
    | (have j1 := eq224 x y
       grind)
    | exact resolve eq16 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq592 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq562 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq562
    | (have j0 := eq562 X0 X1
       grind)
    | exact resolve eq562 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq562
  have eq593 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq592 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq592
    | exact resolve eq592 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq652 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq593 (τ X1) X0
       grind)
    | exact superpose eq593 eq18
    | (have j1 := eq593 (τ X1) X0
       grind)
    | exact resolve eq18 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq593
  have eq892 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq652 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq652
    | exact resolve eq652 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq943 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq892 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq892
    | (have j0 := eq892 X0 X1
       grind)
    | exact resolve eq892 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq1043 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq576
       have i₂ := eq943 y x
       grind)
    | exact superpose eq943 eq576
    | (have j1 := eq943 (σ y) (σ x)
       grind)
    | (have r₁ := eq576
       have r₂ := eq943 y x
       grind)
    | exact resolve eq576 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1044 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1043
  have eq1047 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1044
  have eq1086 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq576
       have i₂ := eq1047
       grind)
    | exact superpose eq1047 eq576
    | exact resolve eq576 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq1047
  have eq1087 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1086
  have eq1088 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1087
  have eq1095 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1088
  have eq1107 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1095
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1095
    | exact resolve eq1095 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095
  have eq1137 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1107
       grind)
    | exact superpose eq1107 eq16
    | exact resolve eq16 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq1149 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1137
       have i₂ := eq943 y x
       grind)
    | exact superpose eq943 eq1137
    | (have j1 := eq943 y x
       grind)
    | (have r₁ := eq1137
       have r₂ := eq943 y x
       grind)
    | exact resolve eq1137 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq1150 : y = (M.op x x) := by grind
  clear eq1149
  have eq1180 : (M.op x y) = (k y x) := by grind
  clear eq1150
  have eq1192 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1137
       have i₂ := eq1180
       grind)
    | exact superpose eq1180 eq1137
    | exact resolve eq1137 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137 eq1180
  have eq1195 : False := by grind
  exact eq1195

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq54 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq54 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq55 (σ X0)
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq57
    | exact resolve eq57 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq57
  have eq80 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq92 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq86
  have eq281 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq92 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq92 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq92 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq92 X0 X1
       grind)
    | exact resolve eq13 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq294 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq281 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq302 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq294 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq294 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq294 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq314 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq302 X0 X1
       have j1 := eq80 X0 (σ X1)
       grind)
    | (have r₁ := eq302 X0 X1
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq302 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq302
  have eq322 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq314 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq314
    | (have j0 := eq314 X0 X1
       grind)
    | exact resolve eq314 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq323 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq322 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq327 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq323 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq323
    | exact resolve eq323 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq323 x y
       grind)
    | exact superpose eq323 eq16
    | exact resolve eq16 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq419 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq327 X0 (τ X1)
       grind)
    | exact superpose eq327 eq17
    | exact resolve eq17 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq327
  have eq437 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq419 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq419
    | exact resolve eq419 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq446 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq437 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq437
    | exact resolve eq437 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq465 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq338
       have i₂ := eq446 x y
       grind)
    | exact superpose eq446 eq338
    | exact resolve eq338 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338 eq446
  have eq466 : False := by grind
  exact eq466

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_pyy_pyx_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq286 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
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
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq286 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq369 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq311 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq370 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq369 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq386 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq370 (σ X1) (σ X0)
       grind)
    | exact superpose eq370 eq15
    | (have j1 := eq370 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq394 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq370 (τ X1) X0
       grind)
    | exact superpose eq370 eq17
    | (have j1 := eq370 (τ X1) X0
       grind)
    | exact resolve eq17 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq370
  have eq443 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq394 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq394
    | exact resolve eq394 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq477 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq443 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq443
    | (have j0 := eq443 X0 X1
       grind)
    | exact resolve eq443 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq602 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq386 x y
       grind)
    | exact superpose eq386 eq16
    | (have j1 := eq386 x y
       grind)
    | exact resolve eq16 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq386 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq622 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq610 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq610
    | (have j0 := eq610 (τ X1) (τ X0)
       grind)
    | exact resolve eq610 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq610
  have eq630 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq622 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq622
    | (have j0 := eq622 X0 X1
       grind)
    | exact resolve eq622 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq632 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq630 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq630
    | (have j0 := eq630 X0 X1
       grind)
    | exact resolve eq630 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq633 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq632 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq632
    | (have j0 := eq632 X0 X1
       grind)
    | exact resolve eq632 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq634 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq633 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq633
    | (have j0 := eq633 X0 X1
       grind)
    | exact resolve eq633 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq730 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq602
       have i₂ := eq477 y x
       grind)
    | exact superpose eq477 eq602
    | (have j1 := eq477 (σ y) (σ x)
       grind)
    | (have r₁ := eq602
       have r₂ := eq477 y x
       grind)
    | exact resolve eq602 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq731 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq730
  have eq739 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (σ y) X0 (σ x)
       have i₂ := eq731
       grind)
    | exact superpose eq731 eq63
    | exact resolve eq63 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq743 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq739 X0 (σ y)
       have i₂ := eq731
       grind)
    | exact superpose eq731 eq739
    | exact resolve eq739 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq760 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq743 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq774 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq731
       have i₂ := eq760 (σ x)
       grind)
    | exact superpose eq760 eq731
    | exact resolve eq731 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq781 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq774
  have eq788 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq781
       grind)
    | exact superpose eq781 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq781
       grind)
    | exact resolve eq12 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq791 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq788 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq801 : ∀ X0 : G, (τ (M.op (σ x) X0)) = (k (τ X0) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22 X0 x
       have i₂ := eq791 X0
       grind)
    | exact superpose eq791 eq22
    | exact resolve eq22 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq791
  have eq830 : (k (τ (σ y)) x) = (τ (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq801 (σ y)
       have i₂ := eq731
       grind)
    | exact superpose eq731 eq801
    | exact resolve eq801 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731 eq801
  have eq850 : (k (τ (σ y)) x) = (τ (σ x)) ∨ x = (M.op x y) := by grind
  clear eq830
  have eq857 : x = (k (τ (σ y)) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq850
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq850
    | exact resolve eq850 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq858 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq857
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq857
    | exact resolve eq857 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq893 : x ≠ x ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq634 y x
       have i₂ := eq858
       grind)
    | exact superpose eq858 eq634
    | (have j0 := eq634 y x
       grind)
    | (have r₁ := eq634 y x
       have r₂ := eq858
       grind)
    | exact resolve eq634 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634 eq858
  have eq896 : x ≠ x ∨ x = (M.op x y) := by grind
  clear eq893
  have eq897 : x = (M.op x y) := by grind
  clear eq896
  have eq910 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 y X0 x
       have i₂ := eq897
       grind)
    | exact superpose eq897 eq63
    | exact resolve eq63 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq913 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq910 X0 y
       have i₂ := eq897
       grind)
    | exact superpose eq897 eq910
    | exact resolve eq910 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq944 : x = (M.op x x) := by
    first
    | (have i₁ := eq897
       have i₂ := eq913 x
       grind)
    | exact superpose eq913 eq897
    | exact resolve eq897 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq950 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq944
       grind)
    | exact superpose eq944 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq944
       grind)
    | exact resolve eq12 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq953 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq950 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq971 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq602
       have i₂ := eq953 y
       grind)
    | exact superpose eq953 eq602
    | exact resolve eq602 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602 eq953
  have eq972 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq971
  have eq977 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq972
       grind)
    | exact superpose eq972 eq16
    | exact resolve eq16 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq986 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq977
       have i₂ := eq913 x
       grind)
    | exact superpose eq913 eq977
    | exact resolve eq977 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913 eq977
  have eq988 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq986
       have i₂ := eq944
       grind)
    | exact superpose eq944 eq986
    | exact resolve eq986 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944 eq986
  have eq989 : False := by grind
  exact eq989
