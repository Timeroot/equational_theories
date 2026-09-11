import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1242`: `x = x ◇ (((y ◇ x) ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_Equation1242 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1242 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1242.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
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
  have eq82 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq196 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq82 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq82 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq82 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq82 X0 X1
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq207 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq196 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq208 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq207 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq210 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq208 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq208
    | (have j0 := eq208 X0 X1
       grind)
    | exact resolve eq208 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq213 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq210 X0 X1
       have j1 := eq204 X1 X0
       grind)
    | (have r₁ := eq210 X1 X0
       have r₂ := eq204 X0 X1
       grind)
    | (have r₁ := eq210 X1 (k X0 X1)
       have r₂ := eq204 X0 X1
       grind)
    | (have r₁ := eq210 X1 X1
       have r₂ := eq204 X1 X1
       grind)
    | exact resolve eq210 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq210
  have eq546 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq213 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq213
    | exact resolve eq213 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq213 y x
       grind)
    | exact superpose eq213 eq16
    | (have j1 := eq213 y x
       grind)
    | exact resolve eq16 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq567 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq546
    | (have j0 := eq546 X0 X1
       grind)
    | exact resolve eq546 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq546
  have eq569 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq567 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq567
    | exact resolve eq567 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq630 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq569 (τ X0) X1
       grind)
    | exact superpose eq569 eq18
    | (have j1 := eq569 (τ X0) X1
       grind)
    | exact resolve eq18 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq569
  have eq793 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq630 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq630
    | exact resolve eq630 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq842 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq793 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq793
    | (have j0 := eq793 X0 X1
       grind)
    | exact resolve eq793 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq957 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq554
       have i₂ := eq842 x y
       grind)
    | exact superpose eq842 eq554
    | (have j1 := eq842 (σ x) (σ y)
       grind)
    | (have r₁ := eq554
       have r₂ := eq842 x y
       grind)
    | exact resolve eq554 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq958 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq957
  have eq1004 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq958
  have eq1009 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq554
       have i₂ := eq1004
       grind)
    | exact superpose eq1004 eq554
    | exact resolve eq554 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq1004
  have eq1010 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1009
  have eq1011 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1010
  have eq1040 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1011
  have eq1047 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1040
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1040
    | exact resolve eq1040 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq1052 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1047
       grind)
    | exact superpose eq1047 eq16
    | exact resolve eq16 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047
  have eq1094 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1052
       have i₂ := eq842 x y
       grind)
    | exact superpose eq842 eq1052
    | (have j1 := eq842 x y
       grind)
    | (have r₁ := eq1052
       have r₂ := eq842 x y
       grind)
    | exact resolve eq1052 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq1095 : x = (M.op y y) := by grind
  clear eq1094
  have eq1102 : (M.op x y) = (k x y) := by grind
  clear eq1095
  have eq1138 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1052
       have i₂ := eq1102
       grind)
    | exact superpose eq1102 eq1052
    | exact resolve eq1052 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052 eq1102
  have eq1141 : False := by grind
  exact eq1141

/-- `Equation1242`: `x = x ◇ (((y ◇ x) ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation1242 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1242 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1242.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq28
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq95 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq37
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq37 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq4457 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq95 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq95 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq95 X0 (M.op (σ X0) X1)
       grind)
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq4466 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4457 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4457
  have eq4467 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4466 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4466
  have eq7545 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ X0 = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4467 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4467
    | exact resolve eq4467 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7579 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq4467 X0 X1
       grind)
    | exact superpose eq4467 eq37
    | (have j1 := eq4467 X0 X1
       grind)
    | exact resolve eq37 eq4467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq4467
  have eq7679 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7579 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7579
    | (have j0 := eq7579 X0 X1
       grind)
    | exact resolve eq7579 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7579
  have eq7687 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7545 X0 X1
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq7545
    | (have j0 := eq7545 X0 X1
       grind)
    | exact resolve eq7545 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7545
  have eq7947 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq7687 X0 X1
       grind)
    | exact superpose eq7687 eq11
    | (have j1 := eq7687 X0 X1
       grind)
    | exact resolve eq11 eq7687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7687
  have eq8066 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7947 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq7947
    | (have j0 := eq7947 X0 X1
       grind)
    | exact resolve eq7947 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7947
  have eq8119 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq8066 X0 (τ X1)
       grind)
    | exact superpose eq8066 eq19
    | (have j1 := eq8066 X0 (τ X1)
       grind)
    | exact resolve eq19 eq8066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq8066
  have eq8475 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (σ (τ X0)) = X1 ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7679 (τ X1) X0
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq7679
    | (have j0 := eq7679 (τ X0) X1
       grind)
    | exact resolve eq7679 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq7679
  have eq8612 : ∀ X0 X1 : G, X0 = X1 ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8475 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8475
    | (have j0 := eq8475 X0 X1
       grind)
    | exact resolve eq8475 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8475
  have eq8652 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ X0 = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8612 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8612
    | (have j0 := eq8612 X0 X1
       grind)
    | exact resolve eq8612 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8612
  have eq8794 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq8652 X0 X1
       grind)
    | exact superpose eq8652 eq11
    | (have j1 := eq8652 X0 X1
       grind)
    | exact resolve eq11 eq8652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8652
  have eq8915 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8794 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq8794
    | (have j0 := eq8794 X0 X1
       grind)
    | exact resolve eq8794 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8794
  have eq9230 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8915 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8915
    | (have j0 := eq8915 (τ (σ X0)) (τ (σ (k X0 X1)))
       grind)
    | exact resolve eq8915 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8915
  have eq9408 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9230 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq9230
    | (have j0 := eq9230 X0 X1
       grind)
    | exact resolve eq9230 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9230
  have eq9419 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9408 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9408
    | (have j0 := eq9408 X0 X1
       grind)
    | exact resolve eq9408 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9408
  have eq10436 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8119 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8119
    | exact resolve eq8119 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8119
  have eq10537 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10436 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq10436
    | (have j0 := eq10436 X0 X1
       grind)
    | exact resolve eq10436 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10436
  have eq11146 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9419 x y
       grind)
    | exact superpose eq9419 eq16
    | (have j1 := eq9419 x y
       grind)
    | exact resolve eq16 eq9419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9419
  have eq11204 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq11146
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq11146
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq11146
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq11146
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11146 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11205 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq11146
       have i₂ := eq10537 y x
       grind)
    | exact superpose eq10537 eq11146
    | (have j1 := eq10537 y x
       grind)
    | (have r₁ := eq11146
       have r₂ := eq10537 y x
       grind)
    | (have r₁ := eq11146
       have r₂ := eq10537 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq11146
       have r₂ := eq10537 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11146 eq10537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10537 eq11146
  have eq11208 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by grind
  clear eq11205
  have eq11209 : x = y ∨ x = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq11208
  have eq11210 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq11204
  have eq11211 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq11210
  have eq11331 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11209
       grind)
    | exact superpose eq11209 eq16
    | exact resolve eq16 eq11209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11209
  have eq11332 : x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq11331
       have r₂ := eq22 x
       grind)
    | exact resolve eq11331 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11331
  have eq11339 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq288 x y
       have i₂ := eq11332
       grind)
    | exact superpose eq11332 eq288
    | (have j0 := eq288 x y
       grind)
    | exact resolve eq288 eq11332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq11332
  have eq11353 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq11339
  have eq11354 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq11353
  have eq11478 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11211
       grind)
    | exact superpose eq11211 eq16
    | exact resolve eq16 eq11211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11211
  have eq11479 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq11478
       have r₂ := eq22 x
       grind)
    | exact resolve eq11478 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11478
  have eq11557 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11354
       grind)
    | exact superpose eq11354 eq16
    | exact resolve eq16 eq11354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11354
  have eq11609 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11557
       have i₂ := eq11479
       grind)
    | exact superpose eq11479 eq11557
    | exact resolve eq11557 eq11479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11479 eq11557
  have eq11613 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq11609
  have eq11614 : (σ x) = (σ y) := by grind
  clear eq11613
  have eq11738 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11614
       grind)
    | exact superpose eq11614 eq16
    | exact resolve eq16 eq11614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11739 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq11614
       grind)
    | exact superpose eq11614 eq10
    | exact resolve eq10 eq11614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11614
  have eq11834 : x = y := by
    first
    | (have i₁ := eq11739
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11739
    | exact resolve eq11739 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11739
  have eq11835 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq11738
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq11738
    | exact resolve eq11738 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq11738
  have eq11836 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq11835
       have i₂ := eq11834
       grind)
    | exact superpose eq11834 eq11835
    | exact resolve eq11835 eq11834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11834 eq11835
  have eq11837 : False := by grind
  exact eq11837

/-- `Equation1255`: `x = x ◇ (((y ◇ y) ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation1255 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1255 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1255.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq76
    | exact resolve eq76 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq77
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq77
    | exact resolve eq77 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq86 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ (k x y) = (M.op x x) := by
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
  have eq87 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17352 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq78 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17353 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq17352
    | exact resolve eq17352 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17352
  have eq17364 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq17353
       have r₂ := eq28
       grind)
    | exact resolve eq17353 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17353
  have eq17368 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq17364
    | exact resolve eq17364 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17364
  have eq17373 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq17368 eq87
    | (have r₁ := eq87
       have r₂ := eq17368
       grind)
    | exact resolve eq87 eq17368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq17368
  have eq17428 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq17373
  have eq17429 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq17428
  have eq17438 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq17429 eq78
    | exact resolve eq78 eq17429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq17429
  have eq17448 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq17438
  have eq17451 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17448
       have r₂ := eq28
       grind)
    | exact resolve eq17448 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17448
  have eq17574 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52
       have i₂ := eq17451
       grind)
    | exact superpose eq17451 eq52
    | exact resolve eq52 eq17451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq17576 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq17451
       grind)
    | exact superpose eq17451 eq86
    | (have r₁ := eq86
       have r₂ := eq17451
       grind)
    | exact resolve eq86 eq17451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq17451
  have eq17630 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq17576
  have eq17631 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq17630
  have eq17645 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq17574
    | exact resolve eq17574 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17574
  have eq17663 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49
       have i₂ := eq17631
       grind)
    | exact superpose eq17631 eq49
    | exact resolve eq49 eq17631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq17631
  have eq17681 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq17663
    | exact resolve eq17663 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17663
  have eq17900 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17681 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq17681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17681
  have eq17901 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17900
  have eq17905 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq17901
    | exact resolve eq17901 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17901
  have eq17916 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq17905
       have r₂ := eq28
       grind)
    | exact resolve eq17905 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17905
  have eq17920 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq17916
    | exact resolve eq17916 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17916
  have eq17933 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq17920 eq17645
    | exact resolve eq17645 eq17920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17645 eq17920
  have eq17982 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq17933
  have eq17989 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq17982
       have r₂ := eq28
       grind)
    | exact resolve eq17982 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17982
  have eq18113 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq17989 eq30
    | exact resolve eq30 eq17989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq17989
  have eq18219 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq18113
    | exact resolve eq18113 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18113
  have eq18220 : x = y := by grind
  clear eq18219
  have eq18239 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq18220
       grind)
    | exact superpose eq18220 eq19
    | exact resolve eq19 eq18220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq18240 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq18220
       grind)
    | exact superpose eq18220 eq25
    | exact resolve eq25 eq18220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq18220
  have eq18341 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq18240
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18240
    | exact resolve eq18240 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq18240
  have eq18356 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18341 eq27
    | exact resolve eq27 eq18341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq18341
  have eq18595 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq18356 eq69
    | exact resolve eq69 eq18356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq18356
  have eq18662 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18595
       have i₂ := eq18239
       grind)
    | exact superpose eq18239 eq18595
    | exact resolve eq18595 eq18239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18239 eq18595
  have eq18671 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18662 eq15
    | exact resolve eq15 eq18662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18662
  have eq18720 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq18671
    | exact resolve eq18671 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq18671
  have eq18729 : False := by grind
  exact eq18729

/-- `Equation1260`: `x = x ◇ (((y ◇ z) ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_pyy_pxy_pyy_pyx_Equation1260 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1260 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1260.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq28 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 X0 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq28 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq28
    | (have j0 := eq28 y
       grind)
    | exact resolve eq28 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29
    | (have j0 := eq29 y
       grind)
    | exact resolve eq29 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq48 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq49 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq52 : ∀ X0 : G, (M.op X0 (M.op (M.op (M.op x y) X0) y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 X0 x y
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op (M.op X2 X3) X0) X3)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 X0 (σ x) (σ y)
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq63 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq10
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq136 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq97 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq97
    | exact resolve eq97 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq216 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op (M.op X1 X2) X0) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 X0 (M.op (M.op (M.op X1 X2) X0) X2)
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq216 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq224 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op y x) ∨ (k y x) = (M.op x x) := by
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
  have eq228 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq229 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq229 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq229 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq231 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq58 eq228
    | exact resolve eq228 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq240 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq136 X0 X0
       have i₂ := eq230 X0
       grind)
    | exact superpose eq230 eq136
    | exact resolve eq136 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq230 (σ X0)
       grind)
    | exact superpose eq230 eq15
    | exact resolve eq15 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq241 X0
       have i₂ := eq230 X0
       grind)
    | exact superpose eq230 eq241
    | exact resolve eq241 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq243 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq240 X0
       have i₂ := eq230 (τ X0)
       grind)
    | exact superpose eq230 eq240
    | exact resolve eq240 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq279 : ∀ X0 X1 X2 X3 : G, (k X1 (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq222 X1 X0 (M.op (M.op (M.op X2 X3) X0) X3)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq222
    | exact resolve eq222 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq49
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq422 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq433 : (σ (k y (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq42
       have i₂ := eq14 sF3 sF1
       grind)
    | exact superpose eq14 eq42
    | (have j1 := eq14 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq42 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq436 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq58
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq58
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq438 : (σ (k (M.op x y) y)) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq34
       have i₂ := eq14 sF1 sF3
       grind)
    | exact superpose eq14 eq34
    | (have j1 := eq14 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq34 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq439 : (σ (k x y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq63
       have i₂ := eq14 sF2 sF3
       grind)
    | exact superpose eq14 eq63
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq63 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq440 : (σ (k x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq439
    | exact resolve eq439 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq441 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq436
    | exact resolve eq436 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq444 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq441
    | exact resolve eq441 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq446 : ∀ X0 X1 : G, y = (M.op y (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x y X0 X1
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X0) X2) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) (M.op X0 (M.op (M.op (M.op X3 X4) X0) X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X0 (M.op (M.op (M.op X1 X2) X0) X2) X3 X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq53
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq449 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) y) = (M.op (M.op (M.op (M.op x y) X0) y) (M.op X0 (M.op (M.op (M.op X1 X2) X0) X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq450 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) (M.op X0 (M.op (M.op (M.op X1 X2) X0) X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq451 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X1) (σ x)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq450 X0 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq450
    | exact resolve eq450 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq475 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) y) = (M.op (M.op (M.op (M.op x y) X0) y) X0) := by
    intro X0
    first
    | (have i₁ := eq449 X0 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq449
    | exact resolve eq449 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq476 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X2) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq448 X0 X1 X2 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq448
    | exact resolve eq448 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq1210 : ∀ X0 X1 : G, y ≠ y ∨ y = (k y (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) X1))) := by
    intro X0 X1
    first
    | exact superpose eq446 eq12
    | (have r₁ := eq12 y (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) X1))
       have r₂ := eq446 X0 X1
       grind)
    | exact resolve eq12 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1220 : ∀ X0 X1 : G, y = (k y (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1210 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq1242 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X1) (σ x)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq451 eq12
    | (have r₁ := eq12 (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X1) (σ x)) X1))
       have r₂ := eq451 X0 X1
       grind)
    | exact resolve eq12 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1253 : ∀ X0 X1 : G, (σ y) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X1) (σ x)) X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1242 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242
  have eq1334 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq422 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq422
    | (have j0 := eq422 X0 X1
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq422 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq1544 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ y) X1) (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq474 eq53
    | exact resolve eq53 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq1870 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op y X1) (M.op (M.op (M.op x y) X0) y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq475 eq53
    | exact resolve eq53 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq2939 : ∀ X0 : G, (M.op X0 (M.op (σ y) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq55 eq1544
    | exact resolve eq1544 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1544
  have eq3027 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op (σ y) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq2939 eq12
    | (have r₁ := eq12 X0 (M.op (σ y) X0)
       have r₂ := eq2939 X0
       grind)
    | exact resolve eq12 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2939
  have eq3073 : ∀ X0 : G, (k X0 (M.op (σ y) X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq3027 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3027
  have eq3111 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq3073 eq136
    | exact resolve eq136 eq3073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3073
  have eq5294 : ∀ X0 : G, (M.op X0 (M.op y X0)) = X0 := by
    intro X0
    first
    | exact superpose eq52 eq1870
    | exact resolve eq1870 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1870
  have eq5415 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X1) (M.op y X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op y X0)
       have i₂ := eq5294 X0
       grind)
    | exact superpose eq5294 eq9
    | exact resolve eq9 eq5294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5424 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X1) (M.op y X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq222 X1 X0 (M.op y X0)
       have i₂ := eq5294 X0
       grind)
    | exact superpose eq5294 eq222
    | exact resolve eq222 eq5294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq5294
  have eq11547 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op X0 X1) X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X0 X1) X2
       have i₂ := eq476 X2 X0 X1
       grind)
    | exact superpose eq476 eq9
    | exact resolve eq9 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq12184 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq279 X0 X1 x (M.op X0 X1)
       have i₂ := eq11547 x (M.op X0 X1) X0
       grind)
    | exact superpose eq11547 eq279
    | exact resolve eq279 eq11547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq12185 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1 x (M.op X0 X1)
       have i₂ := eq11547 x (M.op X0 X1) X0
       grind)
    | exact superpose eq11547 eq53
    | exact resolve eq53 eq11547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq12210 : y = (k y (M.op x y)) := by
    first
    | (have i₁ := eq1220 x sF0
       have i₂ := eq11547 x sF0 x
       grind)
    | exact superpose eq11547 eq1220
    | exact resolve eq1220 eq11547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220
  have eq12211 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq446 x sF0
       have i₂ := eq11547 x sF0 x
       grind)
    | exact superpose eq11547 eq446
    | exact resolve eq446 eq11547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12241 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1253 x sF4
       have i₂ := eq11547 x sF4 sF2
       grind)
    | exact superpose eq11547 eq1253
    | exact resolve eq1253 eq11547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253
  have eq12242 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq451 x sF4
       have i₂ := eq11547 x sF4 sF2
       grind)
    | exact superpose eq11547 eq451
    | exact resolve eq451 eq11547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11547
  have eq12362 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq12210 eq433
    | exact resolve eq433 eq12210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq12426 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq12362
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12362
    | exact resolve eq12362 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12362
  have eq12493 : (M.op x y) = (M.op (M.op x y) (M.op y (M.op y y))) := by
    first
    | exact superpose eq12211 eq5415
    | exact resolve eq5415 eq12211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12494 : (M.op x y) = (k (M.op x y) (M.op y (M.op y y))) := by
    first
    | exact superpose eq12211 eq5424
    | exact resolve eq5424 eq12211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5424 eq12211
  have eq12496 : (M.op x y) = (k (M.op x y) y) := by
    first
    | (have i₁ := eq12494
       have i₂ := eq12185 y y
       grind)
    | exact superpose eq12185 eq12494
    | exact resolve eq12494 eq12185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12494
  have eq12497 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq12493
       have i₂ := eq12185 y y
       grind)
    | exact superpose eq12185 eq12493
    | exact resolve eq12493 eq12185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12493
  have eq12520 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq12496 eq438
    | exact resolve eq438 eq12496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq12881 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq12520
    | exact resolve eq12520 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12520
  have eq12956 : (τ (σ y)) = (k (τ (σ y)) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq12241 eq136
    | exact resolve eq136 eq12241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq12241
  have eq12957 : y = (k y (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq39 eq12956
    | exact resolve eq12956 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12956
  have eq12966 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) (τ (σ y))) := by
    first
    | exact superpose eq12242 eq3111
    | exact resolve eq3111 eq12242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3111
  have eq12994 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op y (σ y)))) := by
    first
    | exact superpose eq12242 eq5415
    | exact resolve eq5415 eq12242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5415 eq12242
  have eq12998 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq12994
       have i₂ := eq12185 y sF3
       grind)
    | exact superpose eq12185 eq12994
    | exact resolve eq12994 eq12185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12994
  have eq13015 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) y) := by
    first
    | exact superpose eq39 eq12966
    | exact resolve eq12966 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq12966
  have eq14289 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12185 X0 (M.op X1 X0)
       have i₂ := eq12185 X1 X0
       grind)
    | exact superpose eq12185 eq12185
    | exact resolve eq12185 eq12185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15361 : ∀ X0 : G, y = (M.op y (M.op (M.op x y) (M.op (M.op X0 x) x))) := by
    intro X0
    first
    | (have i₁ := eq446 X0 x
       have i₂ := eq14289 x X0
       grind)
    | exact superpose eq14289 eq446
    | exact resolve eq446 eq14289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq15375 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq451 x sF2
       have i₂ := eq14289 sF2 x
       grind)
    | exact superpose eq14289 eq451
    | exact resolve eq451 eq14289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq15429 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq15375 x
       have i₂ := eq14289 sF2 x
       grind)
    | exact superpose eq14289 eq15375
    | exact resolve eq15375 eq14289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15375
  have eq15431 : ∀ X0 : G, y = (M.op y (M.op (M.op x y) (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq15361 X0
       have i₂ := eq14289 x X0
       grind)
    | exact superpose eq14289 eq15361
    | exact resolve eq15361 eq14289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14289 eq15361
  have eq19848 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq415 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq415
    | exact resolve eq415 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq19953 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19848 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq19848
    | (have j0 := eq19848 X0 X1
       grind)
    | exact resolve eq19848 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19848
  have eq60889 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1334 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1334
    | (have j0 := eq1334 x y
       grind)
    | exact resolve eq1334 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334
  have eq61015 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq60889
    | exact resolve eq60889 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60889
  have eq61024 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq61015
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq61015
    | exact resolve eq61015 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61015
  have eq61033 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq61024
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq61024
    | exact resolve eq61024 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61024
  have eq61034 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq61033
    | exact resolve eq61033 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61033
  have eq61035 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq61034
       have r₂ := eq27
       grind)
    | exact resolve eq61034 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61034
  have eq61036 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq61035
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq61035
    | exact resolve eq61035 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61035
  have eq61037 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq61036
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq61036
    | exact resolve eq61036 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61036
  have eq61038 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq61037
    | exact resolve eq61037 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61037
  have eq61039 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq61038
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq61038
    | exact resolve eq61038 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61038
  have eq61040 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq61039
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq61039
    | exact resolve eq61039 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61039
  have eq61414 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq61040 eq12185
    | exact resolve eq12185 eq61040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61040
  have eq61458 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq61414
    | exact resolve eq61414 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61414
  have eq61550 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq61458 eq231
    | (have r₁ := eq231
       have r₂ := eq61458
       grind)
    | exact resolve eq231 eq61458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61458
  have eq61660 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq61550
  have eq114940 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq12426 eq12185
    | exact resolve eq12185 eq12426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12426
  have eq120099 : (k (σ x) (M.op (σ y) (σ x))) = (σ (k x (k x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq31 (k x y)
       have i₂ := eq440
       grind)
    | exact superpose eq440 eq31
    | exact resolve eq31 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq120154 : (σ x) = (σ (k x (k x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq120099
       have i₂ := eq12184 sF3 sF2
       grind)
    | exact superpose eq12184 eq120099
    | exact resolve eq120099 eq12184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120099
  have eq145334 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq61660
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq61660
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq61660 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61660
  have eq145396 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq145334
  have eq145416 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq145396
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq145396
    | exact resolve eq145396 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145396
  have eq145421 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq145416
    | exact resolve eq145416 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145416
  have eq145423 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq145421
       have r₂ := eq27
       grind)
    | exact resolve eq145421 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145421
  have eq145425 : (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq145423
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq145423
    | exact resolve eq145423 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145423
  have eq145426 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq145425
  have eq145559 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq145426 eq12185
    | exact resolve eq12185 eq145426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145426
  have eq145627 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq145559
    | exact resolve eq145559 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145559
  have eq145628 : y = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq145627
  have eq145819 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12185 y x
       have i₂ := eq145628
       grind)
    | exact superpose eq145628 eq12185
    | exact resolve eq12185 eq145628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145628
  have eq145863 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq145819
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq145819
    | exact resolve eq145819 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145819
  have eq145931 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y x) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq224
       have i₂ := eq145863
       grind)
    | exact superpose eq145863 eq224
    | (have r₁ := eq224
       have r₂ := eq145863
       grind)
    | exact resolve eq224 eq145863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145954 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq242 x
       have i₂ := eq145863
       grind)
    | exact superpose eq145863 eq242
    | exact resolve eq242 eq145863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145863
  have eq146053 : (M.op x y) = (k y x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq145931
  have eq146060 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq145954
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq145954
    | exact resolve eq145954 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145954
  have eq146063 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq146060
    | exact resolve eq146060 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146060
  have eq160552 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq444
       have i₂ := eq146053
       grind)
    | exact superpose eq146053 eq444
    | exact resolve eq444 eq146053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444 eq146053
  have eq160577 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq160552
    | exact resolve eq160552 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160552
  have eq160578 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq160577
       have r₂ := eq27
       grind)
    | exact resolve eq160577 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160577
  have eq487224 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq160578 eq12185
    | exact resolve eq12185 eq160578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160578
  have eq487228 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq487224
    | exact resolve eq487224 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487224
  have eq487229 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq487228
  have eq487241 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq487229 eq146063
    | exact resolve eq146063 eq487229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146063 eq487229
  have eq487320 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq487241
  have eq487338 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq487320
       have r₂ := eq27
       grind)
    | exact resolve eq487320 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487320
  have eq487626 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12185 y x
       have i₂ := eq487338
       grind)
    | exact superpose eq487338 eq12185
    | exact resolve eq12185 eq487338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487338
  have eq487890 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq487626
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq487626
    | exact resolve eq487626 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487626
  have eq487891 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq487890
  have eq488076 : y = (k y (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq487891 eq12957
    | exact resolve eq12957 eq487891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12957
  have eq488087 : (τ (σ x)) = (k (τ (σ x)) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq487891 eq13015
    | exact resolve eq13015 eq487891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13015 eq487891
  have eq488249 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq488087
    | exact resolve eq488087 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488087
  have eq488252 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq488076
    | exact resolve eq488076 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488076
  have eq489151 : x = (M.op y x) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq488249
       grind)
    | exact superpose eq488249 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq488249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq489153 : (σ x) = (σ (M.op y x)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19953 x y
       have i₂ := eq488249
       grind)
    | exact superpose eq488249 eq19953
    | (have j0 := eq19953 x y
       grind)
    | exact resolve eq19953 eq488249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19953 eq488249
  have eq489154 : (σ x) = (σ (M.op y x)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq489153
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq489153
    | exact resolve eq489153 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489153
  have eq489155 : x = (M.op x y) ∨ x = (M.op y x) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq489151
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq489151
    | exact resolve eq489151 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489151
  have eq489156 : (M.op y x) = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq489155
  have eq489160 : x = (M.op x y) ∨ (σ x) = (σ (M.op y x)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq489154
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq489154
    | exact resolve eq489154 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489154
  have eq489161 : (σ x) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ (M.op y x) = (M.op y y) := by grind
  clear eq489160
  have eq489267 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq488252
       grind)
    | exact superpose eq488252 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq488252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq489273 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq489267
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq489267
    | exact resolve eq489267 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489267
  have eq489278 : y = (M.op y x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq489273
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq489273
    | exact resolve eq489273 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489273
  have eq531540 : (k (σ x) (σ x)) = (σ (k x (M.op y x))) ∨ x = (M.op x y) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq31 (M.op y x)
       have i₂ := eq489161
       grind)
    | exact superpose eq489161 eq31
    | exact resolve eq31 eq489161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq489161
  have eq531546 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq531540
       have i₂ := eq12184 y x
       grind)
    | exact superpose eq12184 eq531540
    | exact resolve eq531540 eq12184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12184 eq531540
  have eq531553 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq531546
       have i₂ := eq230 sF2
       grind)
    | exact superpose eq230 eq531546
    | exact resolve eq531546 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531546
  have eq531555 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq531553
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq531553
    | exact resolve eq531553 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531553
  have eq531599 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) ∨ (M.op y x) = (M.op y y) := by
    first
    | exact superpose eq531555 eq243
    | exact resolve eq243 eq531555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243 eq531555
  have eq531679 : (M.op y x) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq38 eq531599
    | exact resolve eq531599 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq531599
  have eq532172 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12185 y x
       have i₂ := eq489278
       grind)
    | exact superpose eq489278 eq12185
    | exact resolve eq12185 eq489278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489278
  have eq532189 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq532172
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq532172
    | exact resolve eq532172 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532172
  have eq532190 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq532189
  have eq532198 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y x) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq224
       have i₂ := eq532190
       grind)
    | exact superpose eq532190 eq224
    | (have r₁ := eq224
       have r₂ := eq532190
       grind)
    | exact resolve eq224 eq532190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq532190
  have eq532716 : (M.op x y) = (k y x) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq532198
  have eq584358 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq488252
       have i₂ := eq532716
       grind)
    | exact superpose eq532716 eq488252
    | exact resolve eq488252 eq532716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488252 eq532716
  have eq584380 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq584358
  have eq584498 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12185 y x
       have i₂ := eq584380
       grind)
    | exact superpose eq584380 eq12185
    | exact resolve eq12185 eq584380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584380
  have eq584590 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq584498
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq584498
    | exact resolve eq584498 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584498
  have eq584591 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq584590
  have eq584715 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq584591 eq12497
    | exact resolve eq12497 eq584591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12497
  have eq584728 : ∀ X0 : G, y = (M.op y (M.op y (M.op X0 x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq584591 eq15431
    | exact resolve eq15431 eq584591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15431 eq584591
  have eq587357 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq489156
       have i₂ := eq584715
       grind)
    | exact superpose eq584715 eq489156
    | exact resolve eq489156 eq584715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489156
  have eq587370 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq531679
       have i₂ := eq584715
       grind)
    | exact superpose eq584715 eq531679
    | exact resolve eq531679 eq584715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531679 eq584715
  have eq587645 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq587370
  have eq587658 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq587357
  have eq674168 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq12185 y x
       have i₂ := eq587645
       grind)
    | exact superpose eq587645 eq12185
    | exact resolve eq12185 eq587645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587645
  have eq674173 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq674168
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq674168
    | exact resolve eq674168 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674168
  have eq674174 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq674173
  have eq674283 : y = (M.op y (M.op y x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq584728 x
       have i₂ := eq674174
       grind)
    | exact superpose eq674174 eq584728
    | exact resolve eq584728 eq674174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584728 eq674174
  have eq674361 : y = (M.op y (M.op y x)) ∨ x = (M.op x y) := by grind
  clear eq674283
  have eq677631 : (M.op y x) = (M.op (M.op y x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12185 y (M.op y x)
       have i₂ := eq674361
       grind)
    | exact superpose eq674361 eq12185
    | exact resolve eq12185 eq674361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674361
  have eq708810 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12185 y x
       have i₂ := eq587658
       grind)
    | exact superpose eq587658 eq12185
    | exact resolve eq12185 eq587658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587658
  have eq708821 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq708810
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq708810
    | exact resolve eq708810 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708810
  have eq708822 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq708821
  have eq708867 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq677631
       have i₂ := eq708822
       grind)
    | exact superpose eq708822 eq677631
    | exact resolve eq677631 eq708822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677631 eq708822
  have eq709013 : x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq708867
  have eq709055 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq709013
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq709013
    | exact resolve eq709013 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq709013
  have eq709056 : x = (M.op x y) := by grind
  clear eq709055
  have eq709058 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq709056 eq20
    | exact resolve eq20 eq709056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq709515 : y = (k y x) := by
    first
    | exact superpose eq709056 eq12210
    | exact resolve eq12210 eq709056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12210
  have eq709527 : x = (k x y) := by
    first
    | exact superpose eq709056 eq12496
    | exact resolve eq12496 eq709056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12496 eq709056
  have eq742417 : (σ x) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq120154
       have i₂ := eq709527
       grind)
    | exact superpose eq709527 eq120154
    | exact resolve eq120154 eq709527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120154 eq709527
  have eq742960 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq231
       have i₂ := eq709515
       grind)
    | exact superpose eq709515 eq231
    | exact resolve eq231 eq709515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq709515
  have eq743537 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq709058
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq709058
    | exact resolve eq709058 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709058
  have eq744632 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq742417
       have i₂ := eq230 x
       grind)
    | exact superpose eq230 eq742417
    | exact resolve eq742417 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230 eq742417
  have eq744757 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq742960
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq742960
    | exact resolve eq742960 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq742960
  have eq744812 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq743537 eq22
    | exact resolve eq22 eq743537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq744813 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq743537 eq26
    | exact resolve eq26 eq743537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq745009 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (σ (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq743537 eq15429
    | exact resolve eq15429 eq743537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15429
  have eq748739 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq744632
       have i₂ := eq242 x
       grind)
    | exact superpose eq242 eq744632
    | exact resolve eq744632 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242 eq744632
  have eq748820 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq743537 eq744757
    | exact resolve eq744757 eq743537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744757
  have eq749888 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq744813 eq12881
    | exact resolve eq12881 eq744813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12881
  have eq749915 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq744813 eq114940
    | exact resolve eq114940 eq744813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114940
  have eq750284 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq748739
       have i₂ := eq744812
       grind)
    | exact superpose eq744812 eq748739
    | exact resolve eq748739 eq744812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744812 eq748739
  have eq750347 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq743537 eq748820
    | exact resolve eq748820 eq743537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748820
  have eq751447 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq744813 eq749915
    | exact resolve eq749915 eq744813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749915
  have eq751474 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq749888
       have r₂ := eq27
       grind)
    | exact resolve eq749888 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749888
  have eq751585 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq743537 eq750284
    | exact resolve eq750284 eq743537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750284
  have eq751634 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq743537 eq750347
    | exact resolve eq750347 eq743537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750347
  have eq751748 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq751447
       have r₂ := eq27
       grind)
    | exact resolve eq751447 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751447
  have eq751791 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq743537 eq751585
    | exact resolve eq751585 eq743537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751585
  have eq751851 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq744813 eq751748
    | exact resolve eq751748 eq744813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751748
  have eq751866 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq751791
       have r₂ := eq27
       grind)
    | exact resolve eq751791 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751791
  have eq751896 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq743537 eq751866
    | exact resolve eq751866 eq743537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743537 eq751866
  have eq768402 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq751851 eq751634
    | (have r₁ := eq751634
       have r₂ := eq751851
       grind)
    | exact resolve eq751634 eq751851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751634 eq751851
  have eq768403 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq768402
  have eq768404 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq768403
  have eq768941 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq768404 eq12185
    | exact resolve eq12185 eq768404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768404
  have eq769118 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq744813 eq768941
    | exact resolve eq768941 eq744813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768941
  have eq769193 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq769118
       have r₂ := eq27
       grind)
    | exact resolve eq769118 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769118
  have eq769218 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq769193 eq27
    | exact resolve eq27 eq769193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq769324 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq769193 eq12998
    | exact resolve eq12998 eq769193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12998
  have eq770266 : (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq769193 eq744813
    | exact resolve eq744813 eq769193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744813
  have eq770320 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op X0 (σ (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq769193 eq745009
    | exact resolve eq745009 eq769193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745009 eq769193
  have eq772211 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq769324 eq751474
    | exact resolve eq751474 eq769324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751474
  have eq772254 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq769324 eq751896
    | exact resolve eq751896 eq769324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751896 eq769324
  have eq777635 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq772211 eq12185
    | exact resolve eq12185 eq772211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12185 eq772211
  have eq777824 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq770266 eq777635
    | exact resolve eq777635 eq770266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770266 eq777635
  have eq777864 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq777824
       have r₂ := eq769218
       grind)
    | exact resolve eq777824 eq769218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777824
  have eq777998 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq777864 eq772254
    | exact resolve eq772254 eq777864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772254
  have eq778147 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq777998
       have r₂ := eq769218
       grind)
    | exact resolve eq777998 eq769218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777998
  have eq778711 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq778147 eq770320
    | exact resolve eq770320 eq778147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770320 eq778147
  have eq779172 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq777864 eq778711
    | exact resolve eq778711 eq777864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778711
  have eq779239 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq777864 eq779172
    | exact resolve eq779172 eq777864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777864 eq779172
  have eq779267 : False := by grind
  exact eq779267

/-- `Equation1260`: `x = x ◇ (((y ◇ z) ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_x_pxy_x_pyx_Equation1260 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1260 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1260.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op X0 (M.op (M.op (M.op x y) X0) y)) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 X0 (M.op (M.op (M.op X2 X3) X0) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op (M.op X1 X2) X0) X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 X0 (M.op (M.op (M.op X1 X2) X0) X2)
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq65 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq68 : y ≠ (M.op x y) ∨ y = (M.op y x) ∨ y = (k y x) := by
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
  have eq69 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq78 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq86 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq76
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq76
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq91
    | exact resolve eq91 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq101
    | exact resolve eq101 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq129 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq142 : (σ (k y (k (M.op x y) y))) = (k (σ y) (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq129 eq36
    | exact resolve eq36 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq224 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X1) (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 X1 X2 X3 : G, (k X1 (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq66 X1 X0 (M.op (M.op (M.op X2 X3) X0) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq66
    | exact resolve eq66 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq629 : ∀ X0 X1 : G, y = (M.op y (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y X0 X1
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq630 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X1) (σ x)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq632 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X0) X2) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) (M.op X0 (M.op (M.op (M.op X3 X4) X0) X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X0 (M.op (M.op (M.op X1 X2) X0) X2) X3 X4
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op (M.op X0 X2) (M.op (M.op (M.op x y) X0) y)))) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq640 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op (M.op X0 X2) (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y))))) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq658 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X2) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq632 X0 X1 X2 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq632
    | exact resolve eq632 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq1004 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq84 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq5552 : ∀ X0 X1 X2 : G, (k X1 (M.op (M.op (M.op X0 X1) X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 X1 (M.op X0 X1) X2
       have i₂ := eq658 X2 X0 X1
       grind)
    | exact superpose eq658 eq66
    | exact resolve eq66 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq5553 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op X0 X1) X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X0 X1) X2
       have i₂ := eq658 X2 X0 X1
       grind)
    | exact superpose eq658 eq14
    | exact resolve eq14 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq5647 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X1) X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq639 eq5552
    | exact resolve eq5552 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639 eq5552
  have eq5871 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq376 X0 X1 x (M.op X0 X1)
       have i₂ := eq5553 x (M.op X0 X1) X0
       grind)
    | exact superpose eq5553 eq376
    | exact resolve eq376 eq5553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq5872 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1 x (M.op X0 X1)
       have i₂ := eq5553 x (M.op X0 X1) X0
       grind)
    | exact superpose eq5553 eq52
    | exact resolve eq52 eq5553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq5883 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq629 x sF0
       have i₂ := eq5553 x sF0 x
       grind)
    | exact superpose eq5553 eq629
    | exact resolve eq629 eq5553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq5896 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq630 x sF4
       have i₂ := eq5553 x sF4 sF2
       grind)
    | exact superpose eq5553 eq630
    | exact resolve eq630 eq5553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630 eq5553
  have eq5931 : y ≠ y ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq5883 eq13
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq5883
       grind)
    | exact resolve eq13 eq5883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5932 : ∀ X0 : G, (M.op X0 (M.op (M.op y X0) (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq5883 eq14
    | exact resolve eq14 eq5883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5955 : (M.op x y) = (k (M.op x y) (M.op y (M.op x y))) := by
    first
    | exact superpose eq5883 eq5647
    | exact resolve eq5647 eq5883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5956 : y = (k y (M.op x y)) := by grind
  clear eq5931
  have eq5957 : (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq5883 eq5955
    | exact resolve eq5955 eq5883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5883 eq5955
  have eq6085 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5896 eq13
    | (have r₁ := eq13 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq5896
       grind)
    | exact resolve eq13 eq5896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6086 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) X0) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq5896 eq14
    | exact resolve eq14 eq5896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6110 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq5896 eq5647
    | exact resolve eq5647 eq5896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5647
  have eq6111 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by grind
  clear eq6085
  have eq6112 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq5896 eq6110
    | exact resolve eq6110 eq5896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5896 eq6110
  have eq6127 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq5956 eq78
    | exact resolve eq78 eq5956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq5956
  have eq6143 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq6127
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6127
    | exact resolve eq6127 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6127
  have eq6145 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq5957 eq129
    | exact resolve eq129 eq5957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5957
  have eq6160 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq6145
    | exact resolve eq6145 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6145
  have eq7936 : (σ (k y (k (M.op x y) y))) = (M.op (k (σ (M.op x y)) (σ y)) (σ y)) ∨ (σ y) = (M.op (k (σ (M.op x y)) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq129 eq86
    | exact resolve eq86 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq129
  have eq7990 : (σ (k y (k (M.op x y) y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (k (σ (M.op x y)) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq6160 eq7936
    | exact resolve eq7936 eq6160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7936
  have eq8023 : (k (σ y) (k (σ (M.op x y)) (σ y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (k (σ (M.op x y)) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq142 eq7990
    | exact resolve eq7990 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq7990
  have eq8046 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (k (σ (M.op x y)) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq6160 eq8023
    | exact resolve eq8023 eq6160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8023
  have eq8066 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (k (σ (M.op x y)) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq6143 eq8046
    | exact resolve eq8046 eq6143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6143 eq8046
  have eq8081 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq6160 eq8066
    | exact resolve eq8066 eq6160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8066
  have eq8082 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (k (σ (M.op x y)) (σ y))) := by grind
  clear eq8081
  have eq8097 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq6160 eq8082
    | exact resolve eq8082 eq6160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8082
  have eq8215 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5871 X0 (M.op X1 X0)
       have i₂ := eq5872 X1 X0
       grind)
    | exact superpose eq5872 eq5871
    | exact resolve eq5871 eq5872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5871
  have eq14372 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (M.op (M.op X0 (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y))))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq8097 eq640
    | exact resolve eq640 eq8097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640 eq8097
  have eq14401 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq224 eq14372
    | exact resolve eq14372 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq14372
  have eq14546 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1004 y x
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq1004
    | (have j0 := eq1004 y x
       grind)
    | exact resolve eq1004 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq14663 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14546
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14546
    | exact resolve eq14546 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14546
  have eq14771 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14663
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14663
    | exact resolve eq14663 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14663
  have eq14879 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14771
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14771
    | exact resolve eq14771 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14771
  have eq14971 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq14879
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14879
    | exact resolve eq14879 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14879
  have eq15058 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq14971
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14971
    | exact resolve eq14971 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14971
  have eq15127 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq15058
    | exact resolve eq15058 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15058
  have eq41576 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41586 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq41576
    | exact resolve eq41576 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41576
  have eq41596 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq41586
       have r₂ := eq27
       grind)
    | exact resolve eq41586 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41586
  have eq41600 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq41596
    | exact resolve eq41596 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41596
  have eq41609 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq41600 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq41600
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq41600
       grind)
    | exact resolve eq13 eq41600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41600
  have eq41696 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq41609
  have eq47964 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq41696 eq83
    | exact resolve eq83 eq41696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41696
  have eq47991 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq47964
    | exact resolve eq47964 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47964
  have eq47995 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq47991
       have r₂ := eq68
       grind)
    | exact resolve eq47991 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq47991
  have eq48007 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq47995
       grind)
    | exact superpose eq47995 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq47995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48013 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1004 x y
       have i₂ := eq47995
       grind)
    | exact superpose eq47995 eq1004
    | (have j0 := eq1004 x y
       grind)
    | exact resolve eq1004 eq47995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47995
  have eq48017 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq48013
  have eq48018 : y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq48007
  have eq48023 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq48017
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48017
    | exact resolve eq48017 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48017
  have eq48029 : y = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq48018
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq48018
    | exact resolve eq48018 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48018
  have eq48043 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq48023
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq48023
    | exact resolve eq48023 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48023
  have eq48056 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq48043
    | exact resolve eq48043 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48043
  have eq48057 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq48056
  have eq48067 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq48057
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq48057
    | exact resolve eq48057 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48057
  have eq48080 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq48067
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48067
    | exact resolve eq48067 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48067
  have eq48173 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5872 y x
       have i₂ := eq48029
       grind)
    | exact superpose eq48029 eq5872
    | exact resolve eq5872 eq48029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48029
  have eq48208 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq48173
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq48173
    | exact resolve eq48173 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48173
  have eq48266 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq48208 eq27
    | exact resolve eq27 eq48208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50021 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq48080 eq5872
    | exact resolve eq5872 eq48080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48080
  have eq50056 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq50021
    | exact resolve eq50021 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50021
  have eq50191 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8215 x y
       have i₂ := eq50056
       grind)
    | exact superpose eq50056 eq8215
    | exact resolve eq8215 eq50056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8215 eq50056
  have eq51206 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1004 x y
       have i₂ := eq50191
       grind)
    | exact superpose eq50191 eq1004
    | (have j0 := eq1004 x y
       grind)
    | exact resolve eq1004 eq50191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004 eq50191
  have eq51210 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq51206
  have eq51216 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq51210
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq51210
    | exact resolve eq51210 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51210
  have eq51234 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq51216
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq51216
    | exact resolve eq51216 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51216
  have eq51247 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq51234
    | exact resolve eq51234 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51234
  have eq51248 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq51247
  have eq51258 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq51248
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq51248
    | exact resolve eq51248 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51248
  have eq51271 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq51258
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq51258
    | exact resolve eq51258 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51258
  have eq51763 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51271 eq5872
    | exact resolve eq5872 eq51271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51271
  have eq51804 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq51763
    | exact resolve eq51763 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51763
  have eq51805 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq51804
  have eq51872 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51805 eq27
    | exact resolve eq27 eq51805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51875 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51805 eq69
    | (have r₁ := eq69
       have r₂ := eq51805
       grind)
    | exact resolve eq69 eq51805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq51805
  have eq51933 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq51875
  have eq57116 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51933 eq83
    | exact resolve eq83 eq51933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq51933
  have eq57145 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq57116
    | exact resolve eq57116 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57116
  have eq57616 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq57145 eq5872
    | exact resolve eq5872 eq57145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57145
  have eq57661 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq57616
    | exact resolve eq57616 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57616
  have eq57662 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq57661
  have eq57737 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq57662
       grind)
    | exact superpose eq57662 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq57662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57662
  have eq57748 : y = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq57737
  have eq57759 : y = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq57748
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq57748
    | exact resolve eq57748 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57748
  have eq58046 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5872 y x
       have i₂ := eq57759
       grind)
    | exact superpose eq57759 eq5872
    | exact resolve eq5872 eq57759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57759
  have eq58085 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq58046
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq58046
    | exact resolve eq58046 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58046
  have eq58195 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58085 eq6111
    | exact resolve eq6111 eq58085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6111
  have eq58204 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58085 eq48208
    | exact resolve eq48208 eq58085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48208 eq58085
  have eq58213 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq58204
  have eq58245 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58213 eq29
    | exact resolve eq29 eq58213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq58213
  have eq58503 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq58245
    | exact resolve eq58245 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58245
  have eq59417 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58195 eq103
    | exact resolve eq103 eq58195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq58195
  have eq59441 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq59417
  have eq59451 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq59441
       have r₂ := eq48266
       grind)
    | exact resolve eq59441 eq48266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48266 eq59441
  have eq60674 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5872 y x
       have i₂ := eq59451
       grind)
    | exact superpose eq59451 eq5872
    | exact resolve eq5872 eq59451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5872 eq59451
  have eq60713 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq60674
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq60674
    | exact resolve eq60674 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60674
  have eq60714 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq60713
  have eq60787 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq60714 eq20
    | exact resolve eq20 eq60714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60908 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq60714
  have eq60975 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq60787
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq60787
    | exact resolve eq60787 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq60787
  have eq61187 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq60975 eq51872
    | (have r₁ := eq51872
       have r₂ := eq60975
       grind)
    | exact resolve eq51872 eq60975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51872 eq60975
  have eq61224 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq61187
  have eq61422 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61224 eq6112
    | exact resolve eq6112 eq61224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6112 eq61224
  have eq63679 : (τ (σ x)) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61422 eq57
    | exact resolve eq57 eq61422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq61422
  have eq63712 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq63679
    | exact resolve eq63679 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq63679
  have eq64402 : x = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq63712
       grind)
    | exact superpose eq63712 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq63712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63712
  have eq64413 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq64402
  have eq64424 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq64413
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq64413
    | exact resolve eq64413 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64413
  have eq64425 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq64424
  have eq65123 : x = (M.op x (M.op x (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5932 x
       have i₂ := eq64425
       grind)
    | exact superpose eq64425 eq5932
    | exact resolve eq5932 eq64425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5932 eq64425
  have eq81795 : x = (M.op x (M.op x y)) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq58503 eq65123
    | exact resolve eq65123 eq58503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65123
  have eq81893 : x = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq81795
  have eq81930 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq81893
       have r₂ := eq60908
       grind)
    | exact resolve eq81893 eq60908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81893
  have eq81936 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq81930
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq81930
    | exact resolve eq81930 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81930
  have eq81940 : x = (M.op x y) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq58503 eq81936
    | exact resolve eq81936 eq58503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58503 eq81936
  have eq82041 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq81940
  have eq82075 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq82041
       have r₂ := eq60908
       grind)
    | exact resolve eq82041 eq60908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60908 eq82041
  have eq82078 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq82075
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq82075
    | exact resolve eq82075 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq82075
  have eq82079 : x = (M.op x y) := by grind
  clear eq82078
  have eq82653 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq82079 eq20
    | exact resolve eq20 eq82079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq82079
  have eq82858 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq82653
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq82653
    | exact resolve eq82653 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq82653
  have eq82933 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq82858 eq26
    | exact resolve eq26 eq82858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq82991 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq82858 eq15127
    | exact resolve eq15127 eq82858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15127 eq82858
  have eq83121 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq82991
       have r₂ := eq6160
       grind)
    | exact resolve eq82991 eq6160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6160 eq82991
  have eq83181 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq83121
       have r₂ := eq27
       grind)
    | exact resolve eq83121 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83121
  have eq85462 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq82933 eq14401
    | exact resolve eq14401 eq82933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14401
  have eq85569 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq85462
       have r₂ := eq27
       grind)
    | exact resolve eq85462 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85462
  have eq85744 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq83181 eq6086
    | exact resolve eq6086 eq83181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6086 eq83181
  have eq85878 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq85569 eq85744
    | exact resolve eq85744 eq85569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85744
  have eq85906 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq82933 eq85878
    | exact resolve eq85878 eq82933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85878
  have eq85926 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq85569 eq85906
    | exact resolve eq85906 eq85569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85569 eq85906
  have eq85940 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq82933 eq85926
    | exact resolve eq85926 eq82933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82933 eq85926
  have eq85950 : False := by grind
  exact eq85950

/-- `Equation1260`: `x = x ◇ (((y ◇ z) ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_x_pxy_y_pyx_Equation1260 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1260 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1260.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op X0 (M.op (M.op (M.op x y) X0) y)) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 X0 (M.op (M.op (M.op X2 X3) X0) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op (M.op X1 X2) X0) X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 X0 (M.op (M.op (M.op X1 X2) X0) X2)
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq66 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq78 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq80 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq78
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq78
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq78 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq93
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq93
    | exact resolve eq93 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq21 eq103
    | exact resolve eq103 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq368 : ∀ X0 X1 X2 X3 : G, (k X1 (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq67 X1 X0 (M.op (M.op (M.op X2 X3) X0) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq67
    | exact resolve eq67 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X0) X2) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) (M.op X0 (M.op (M.op (M.op X3 X4) X0) X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X0 (M.op (M.op (M.op X1 X2) X0) X2) X3 X4
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq444 : ∀ X0 X1 : G, y = (M.op y (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 x y X0 X1
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq445 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X1) (σ x)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X2 X1) (M.op (M.op X0 X2) (M.op (M.op (M.op X3 X4) X0) X4)))) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X2 X1 X0 (M.op (M.op (M.op X3 X4) X0) X4)
       have i₂ := eq14 X0 X3 X4
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op (M.op X0 X2) (M.op (M.op (M.op x y) X0) y)))) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq471 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X2) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq440 X0 X1 X2 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq440
    | exact resolve eq440 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq994 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (σ X0) (M.op (σ (k X0 X1)) (M.op (M.op (M.op X2 X3) (σ X1)) X3))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (σ X1) (σ X0) X2 X3
       have i₂ := eq86 X0 X1
       grind)
    | exact superpose eq86 eq53
    | (have j1 := eq86 X0 X1
       grind)
    | exact resolve eq53 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq5647 : ∀ X0 X1 X2 : G, (k X1 (M.op (M.op (M.op X0 X1) X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X1 (M.op X0 X1) X2
       have i₂ := eq471 X2 X0 X1
       grind)
    | exact superpose eq471 eq67
    | exact resolve eq67 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq5648 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op X0 X1) X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X0 X1) X2
       have i₂ := eq471 X2 X0 X1
       grind)
    | exact superpose eq471 eq14
    | exact resolve eq14 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq5743 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X1) X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq448 eq5647
    | exact resolve eq5647 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448 eq5647
  have eq5968 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq368 X0 X1 x (M.op X0 X1)
       have i₂ := eq5648 x (M.op X0 X1) X0
       grind)
    | exact superpose eq5648 eq368
    | exact resolve eq368 eq5648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq5969 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1 x (M.op X0 X1)
       have i₂ := eq5648 x (M.op X0 X1) X0
       grind)
    | exact superpose eq5648 eq53
    | exact resolve eq53 eq5648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq5979 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq444 x sF0
       have i₂ := eq5648 x sF0 x
       grind)
    | exact superpose eq5648 eq444
    | exact resolve eq444 eq5648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq5992 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq445 x sF4
       have i₂ := eq5648 x sF4 sF2
       grind)
    | exact superpose eq5648 eq445
    | exact resolve eq445 eq5648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq6026 : y ≠ y ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq5979 eq13
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq5979
       grind)
    | exact resolve eq13 eq5979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6050 : y = (k y (M.op x y)) := by grind
  clear eq6026
  have eq6178 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5992 eq13
    | (have r₁ := eq13 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq5992
       grind)
    | exact resolve eq13 eq5992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6202 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq5992 eq5743
    | exact resolve eq5743 eq5992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5743
  have eq6203 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by grind
  clear eq6178
  have eq6204 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq5992 eq6202
    | exact resolve eq6202 eq5992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5992 eq6202
  have eq6219 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq6050 eq80
    | exact resolve eq80 eq6050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6050
  have eq6233 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq6219
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq6219
    | exact resolve eq6219 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6219
  have eq6586 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X1 X2) (M.op X0 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq447 X0 X2 X1 x (M.op X0 X1)
       have i₂ := eq5648 x (M.op X0 X1) X0
       grind)
    | exact superpose eq5648 eq447
    | exact resolve eq447 eq5648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447 eq5648
  have eq7960 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5969 X0 (M.op X1 X0)
       have i₂ := eq5969 X1 X0
       grind)
    | exact superpose eq5969 eq5969
    | exact resolve eq5969 eq5969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27303 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (k (σ y) (σ (M.op x y))) (M.op (M.op (M.op X0 X1) (σ (M.op x y))) X1))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq80 eq994
    | (have j0 := eq994 y (M.op x y) x x
       grind)
    | exact resolve eq994 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq994
  have eq27696 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (k (σ y) (σ (M.op x y))) (M.op (M.op (M.op X0 X1) (σ (M.op x y))) X1))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq21 eq27303
    | (have j0 := eq27303 X0 X1
       grind)
    | exact resolve eq27303 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27303
  have eq27899 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (M.op (M.op X0 X1) (σ (M.op x y))) X1))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq6233 eq27696
    | exact resolve eq27696 eq6233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6233 eq27696
  have eq28090 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (M.op (M.op X0 X1) (σ (M.op x y))) X1))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq27899 X0 X1
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq27899
    | (have j0 := eq27899 X0 X1
       grind)
    | exact resolve eq27899 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27899
  have eq28261 : ∀ X0 X1 : G, (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (M.op (M.op (M.op X0 X1) (σ (M.op x y))) X1))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq21 eq28090
    | (have j0 := eq28090 X0 X1
       grind)
    | exact resolve eq28090 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28090
  have eq28388 : ∀ X0 X1 : G, (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (M.op (M.op (M.op X0 X1) (σ (M.op x y))) X1))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq28261 X0 X1
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq28261
    | (have j0 := eq28261 X0 X1
       grind)
    | exact resolve eq28261 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28261
  have eq28506 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (M.op (M.op (M.op X0 X1) (σ (M.op x y))) X1))) := by
    intro X0 X1
    first
    | exact superpose eq21 eq28388
    | (have j0 := eq28388 X0 X1
       grind)
    | exact resolve eq28388 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28388
  have eq28611 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op (M.op (M.op X0 X1) (σ (M.op x y))) X1))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq28506 X0 X1
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq28506
    | (have j0 := eq28506 X0 X1
       grind)
    | exact resolve eq28506 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq28506
  have eq53778 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq104 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53786 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq53778
    | exact resolve eq53778 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53778
  have eq53797 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq53786
       have r₂ := eq28
       grind)
    | exact resolve eq53786 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53786
  have eq53864 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq53797 eq5969
    | exact resolve eq5969 eq53797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53797
  have eq53900 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq53864
    | exact resolve eq53864 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53864
  have eq54025 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq53900 eq5969
    | exact resolve eq5969 eq53900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53900
  have eq54055 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq54025
    | exact resolve eq54025 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54025
  have eq54056 : y = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq54055
  have eq54155 : y = (M.op x x) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5968 y x
       have i₂ := eq54056
       grind)
    | exact superpose eq54056 eq5968
    | exact resolve eq5968 eq54056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54156 : x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5969 y x
       have i₂ := eq54056
       grind)
    | exact superpose eq54056 eq5969
    | exact resolve eq5969 eq54056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54056
  have eq54192 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54156
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq54156
    | exact resolve eq54156 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54156
  have eq54319 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5969 x x
       have i₂ := eq54192
       grind)
    | exact superpose eq54192 eq5969
    | exact resolve eq5969 eq54192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54192
  have eq54349 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54319
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq54319
    | exact resolve eq54319 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54319
  have eq54350 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq54349
  have eq54428 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq54350 eq6203
    | exact resolve eq6203 eq54350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6203
  have eq54429 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq54350 eq6204
    | exact resolve eq6204 eq54350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6204 eq54350
  have eq54603 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq104 eq54428
    | exact resolve eq54428 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq54428
  have eq54640 : (τ (σ x)) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq54429 eq58
    | exact resolve eq58 eq54429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq54429
  have eq54662 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq54640
    | exact resolve eq54640 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq54640
  have eq56369 : x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq54662
       grind)
    | exact superpose eq54662 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq54662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54662
  have eq56384 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56369
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56369
    | exact resolve eq56369 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56369
  have eq56385 : x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq56384
  have eq64852 : x = (k x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5968 x x
       have i₂ := eq54155
       grind)
    | exact superpose eq54155 eq5968
    | exact resolve eq5968 eq54155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5968 eq54155
  have eq64883 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq64852
  have eq64917 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq64883
       grind)
    | exact superpose eq64883 eq45
    | exact resolve eq45 eq64883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq64883
  have eq64953 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq64917
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq64917
    | exact resolve eq64917 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64917
  have eq65017 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq64953 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq64953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64953
  have eq65025 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq65017
    | exact resolve eq65017 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65017
  have eq65026 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq65025
  have eq67382 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq65026 eq7960
    | exact resolve eq7960 eq65026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65026
  have eq67407 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq67382
    | exact resolve eq67382 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67382
  have eq67408 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq67407
  have eq67529 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq67408 eq5969
    | exact resolve eq5969 eq67408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72564 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7960 y y
       have i₂ := eq56385
       grind)
    | exact superpose eq56385 eq7960
    | exact resolve eq7960 eq56385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56385
  have eq72589 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72564
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq72564
    | exact resolve eq72564 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72564
  have eq72590 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq72589
  have eq72697 : ∀ X0 : G, x = (M.op x (M.op x (M.op X0 y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq6586 X0 y x
       have i₂ := eq72590
       grind)
    | exact superpose eq72590 eq6586
    | exact resolve eq6586 eq72590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6586 eq72590
  have eq2182800 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq5969 y x
       have i₂ := eq54603
       grind)
    | exact superpose eq54603 eq5969
    | exact resolve eq5969 eq54603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54603
  have eq2183703 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2182800
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2182800
    | exact resolve eq2182800 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2182800
  have eq2183704 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2183703
  have eq2184462 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq5969 x x
       have i₂ := eq2183704
       grind)
    | exact superpose eq2183704 eq5969
    | exact resolve eq5969 eq2183704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5969 eq2183704
  have eq2185157 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2184462
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2184462
    | exact resolve eq2184462 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2184462
  have eq2185158 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq2185157
  have eq2185261 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2185158 eq30
    | exact resolve eq30 eq2185158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2185158
  have eq2187346 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq2185261
    | exact resolve eq2185261 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2185261
  have eq2187604 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2187346 eq5979
    | exact resolve eq5979 eq2187346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5979
  have eq2188144 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq2215700 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72697 y
       have i₂ := eq2187604
       grind)
    | exact superpose eq2187604 eq72697
    | exact resolve eq72697 eq2187604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72697 eq2187604
  have eq2216458 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq2215700
  have eq2216833 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2216458
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2216458
    | exact resolve eq2216458 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2216458
  have eq2339269 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2187346 eq2216833
    | exact resolve eq2216833 eq2187346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2187346 eq2216833
  have eq2340777 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2339269
       have r₂ := eq2188144
       grind)
    | exact resolve eq2339269 eq2188144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2188144 eq2339269
  have eq2340806 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2340777
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2340777
    | exact resolve eq2340777 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq2340777
  have eq2340807 : x = (M.op x y) := by grind
  clear eq2340806
  have eq2340815 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2340807 eq21
    | exact resolve eq21 eq2340807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2340807
  have eq2341588 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2340815
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2340815
    | exact resolve eq2340815 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2340815
  have eq2341689 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2341588 eq27
    | exact resolve eq27 eq2341588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq2341946 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2341588 eq67408
    | exact resolve eq67408 eq2341588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67408
  have eq2341959 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2341588 eq67529
    | exact resolve eq67529 eq2341588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67529 eq2341588
  have eq2343588 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq2341959
       have r₂ := eq28
       grind)
    | exact resolve eq2341959 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341959
  have eq2343601 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq2341946
       have r₂ := eq28
       grind)
    | exact resolve eq2341946 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341946
  have eq2388830 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2343601 eq28611
    | exact resolve eq28611 eq2343601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28611
  have eq2388981 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2388830
       have i₂ := eq7960 sF1 sF1
       grind)
    | exact superpose eq7960 eq2388830
    | exact resolve eq2388830 eq7960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7960 eq2388830
  have eq2389384 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2343588 eq2388981
    | exact resolve eq2388981 eq2343588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2388981
  have eq2389522 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2343601 eq2389384
    | exact resolve eq2389384 eq2343601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2389384
  have eq2389570 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2343601 eq2389522
    | exact resolve eq2389522 eq2343601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2343601 eq2389522
  have eq2389571 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2389570
  have eq2389582 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2343588 eq2389571
    | exact resolve eq2389571 eq2343588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2389571
  have eq2389583 : (σ (M.op x y)) = (σ y) := by grind
  clear eq2389582
  have eq2390823 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2389583 eq2341689
    | exact resolve eq2341689 eq2389583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341689 eq2389583
  have eq2390834 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2343588 eq2390823
    | exact resolve eq2390823 eq2343588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2343588 eq2390823
  have eq2391105 : False := by grind
  exact eq2391105

/-- `Equation1434`: `x = (x ◇ x) ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_pyx_pxx_pyx_Equation1434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq84 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq277 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq84 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq84 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq84 X1 X1
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq280 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq277 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq281 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq280 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq283 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq281 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq281
    | (have j0 := eq281 X0 X1
       grind)
    | exact resolve eq281 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq287 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq283 X0 X1
       have j1 := eq279 X1 X0
       grind)
    | (have r₁ := eq283 X1 X0
       have r₂ := eq279 X0 X1
       grind)
    | (have r₁ := eq283 (k X1 X0) X1
       have r₂ := eq279 X0 X1
       grind)
    | (have r₁ := eq283 X1 X1
       have r₂ := eq279 X1 X1
       grind)
    | exact resolve eq283 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279 eq283
  have eq524 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq287 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq287
    | exact resolve eq287 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq538 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq287 y x
       grind)
    | exact superpose eq287 eq16
    | (have j1 := eq287 y x
       grind)
    | exact resolve eq16 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq555 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq524 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq524
    | (have j0 := eq524 X0 X1
       grind)
    | exact resolve eq524 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq524
  have eq560 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq555 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq555
    | exact resolve eq555 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq625 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq560 (τ X1) X0
       grind)
    | exact superpose eq560 eq18
    | (have j1 := eq560 (τ X1) X0
       grind)
    | exact resolve eq18 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq560
  have eq842 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq625 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq625
    | exact resolve eq625 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq894 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq842 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq842
    | (have j0 := eq842 X0 X1
       grind)
    | exact resolve eq842 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq991 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq538
       have i₂ := eq894 y x
       grind)
    | exact superpose eq894 eq538
    | (have j1 := eq894 (σ y) (σ x)
       grind)
    | (have r₁ := eq538
       have r₂ := eq894 y x
       grind)
    | exact resolve eq538 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq992 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq991
  have eq1036 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq992
  have eq1043 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq538
       have i₂ := eq1036
       grind)
    | exact superpose eq1036 eq538
    | exact resolve eq538 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538 eq1036
  have eq1044 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1043
  have eq1045 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1044
  have eq1079 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1045
  have eq1091 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1079
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1079
    | exact resolve eq1079 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079
  have eq1096 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1091
       grind)
    | exact superpose eq1091 eq16
    | exact resolve eq16 eq1091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq1137 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1096
       have i₂ := eq894 y x
       grind)
    | exact superpose eq894 eq1096
    | (have j1 := eq894 y x
       grind)
    | (have r₁ := eq1096
       have r₂ := eq894 y x
       grind)
    | exact resolve eq1096 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq1138 : y = (M.op x x) := by grind
  clear eq1137
  have eq1144 : (M.op x y) = (k y x) := by grind
  clear eq1138
  have eq1185 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1096
       have i₂ := eq1144
       grind)
    | exact superpose eq1144 eq1096
    | exact resolve eq1096 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096 eq1144
  have eq1188 : False := by grind
  exact eq1188

/-- `Equation1434`: `x = (x ◇ x) ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_pxy_Equation1434 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1434 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1434.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X1 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq19 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (k X1 X1) ≠ (k X0 X0) := by
    intro X0 X1
    grind
  clear eq18
  have eq21 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X1 X1) = (k X0 X0) := by
    intro X0 X1
    grind
  clear eq19
  have eq22 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
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
  have eq565 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ x = y ∨ (k x x) ≠ (k y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq20 y x
       grind)
    | exact superpose eq20 eq9
    | (have j1 := eq20 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq20 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq20 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : (k x x) ≠ (k y y) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq565
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq565
    | exact resolve eq565 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq1223 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ x = y ∨ (k x x) = (k y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq21 x y
       grind)
    | exact superpose eq21 eq9
    | (have j1 := eq21 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq21 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq21 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1233 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (k x x) = (k y y) := by
    first
    | (have i₁ := eq1223
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq1223
    | exact resolve eq1223 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq1239 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1233
       have i₂ := eq21 (σ x) (σ y)
       grind)
    | exact superpose eq21 eq1233
    | (have j1 := eq21 x y
       grind)
    | (have r₁ := eq1233
       have r₂ := eq21 (σ x) (σ y)
       grind)
    | (have r₁ := eq1233
       have r₂ := eq21 (M.op (σ x) (σ y)) (k (σ x) (σ y))
       grind)
    | (have r₁ := eq1233
       have r₂ := eq21 (k (σ x) (σ y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1233 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1233
  have eq1241 : x = y ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1239
  have eq1317 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1241
       grind)
    | exact superpose eq1241 eq9
    | exact resolve eq9 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq1318 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1317
  have eq1319 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1318
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1318
    | exact resolve eq1318 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318
  have eq1320 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1319
  have eq1321 : (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1320
  have eq1399 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq1321
       grind)
    | exact superpose eq1321 eq10
    | exact resolve eq10 eq1321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321
  have eq1401 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1399
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1399
    | exact resolve eq1399 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399
  have eq1402 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1401
  have eq1406 : (k y y) = (τ (k (σ x) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22 y y
       have i₂ := eq1402
       grind)
    | exact superpose eq1402 eq22
    | exact resolve eq22 eq1402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1453 : (k x x) = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1406
       have i₂ := eq22 x x
       grind)
    | exact superpose eq22 eq1406
    | exact resolve eq1406 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1406
  have eq1475 : (k x x) ≠ (k x x) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq572
       have i₂ := eq1453
       grind)
    | exact superpose eq1453 eq572
    | (have r₁ := eq572
       have r₂ := eq1453
       grind)
    | exact resolve eq572 eq1453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq1453
  have eq1478 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1475
  have eq1482 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1478
       have i₂ := eq20 (σ y) (σ x)
       grind)
    | exact superpose eq20 eq1478
    | (have j1 := eq20 (σ x) (σ y)
       grind)
    | (have r₁ := eq1478
       have r₂ := eq20 (σ y) (σ x)
       grind)
    | (have r₁ := eq1478
       have r₂ := eq20 (M.op (σ x) (σ y)) (k (σ y) (σ x))
       grind)
    | (have r₁ := eq1478
       have r₂ := eq20 (k (σ y) (σ x)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1478 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1478
  have eq1483 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by grind
  clear eq1482
  have eq1484 : x = y ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by grind
  clear eq1483
  have eq1486 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1484
       have r₂ := eq1402
       grind)
    | exact resolve eq1484 eq1402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402 eq1484
  have eq1487 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1486
       grind)
    | exact superpose eq1486 eq9
    | exact resolve eq9 eq1486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1486
  have eq1488 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq1487
  have eq1489 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1488
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1488
    | exact resolve eq1488 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488
  have eq1490 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1489
  have eq1491 : (σ x) = (σ y) := by grind
  clear eq1490
  have eq1493 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq1491
       grind)
    | exact superpose eq1491 eq15
    | exact resolve eq15 eq1491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1491
  have eq1540 : x = y := by
    first
    | (have i₁ := eq1493
       have i₂ := eq15 x
       grind)
    | exact superpose eq15 eq1493
    | exact resolve eq1493 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493
  have eq1543 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1540
       grind)
    | exact superpose eq1540 eq9
    | exact resolve eq9 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1540
  have eq1544 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq1543
  have eq1545 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1544
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1544
    | exact resolve eq1544 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544
  have eq1546 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by grind
  clear eq1545
  have eq1547 : False := by grind
  exact eq1547
