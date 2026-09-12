import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pyx_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq55
    | (have j0 := eq55 (σ X0) (σ X1)
       grind)
    | exact resolve eq55 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq33 (τ X0)
       grind)
    | exact superpose eq33 eq18
    | exact resolve eq18 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq82 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81
    | exact resolve eq81 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq90 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq82
    | exact resolve eq82 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq82
  have eq94 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq90 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X4)) X5)) X0) = X0 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq23 X0 (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X4 X5
       have i₂ := eq23 X0 X1 X2 X3
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq141 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66 y x
       grind)
    | exact superpose eq66 eq16
    | (have j1 := eq66 y x
       grind)
    | exact resolve eq16 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq167 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq9
    | exact resolve eq9 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq106 (σ X0)
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq106
    | exact resolve eq106 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq319 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq206 X0
       grind)
    | exact superpose eq206 eq9
    | exact resolve eq9 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq573 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq141
       have i₂ := eq55 y x
       grind)
    | exact superpose eq55 eq141
    | (have j1 := eq55 (σ y) (σ x)
       grind)
    | exact resolve eq141 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq141
  have eq574 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq573
  have eq644 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op (τ X0) (τ X0))) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq319 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq319
    | exact resolve eq319 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq659 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq644 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq644
    | exact resolve eq644 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq644
  have eq727 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq659 (M.op X1 X0) X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq659
    | exact resolve eq659 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq659 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq659
    | exact resolve eq659 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq896 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq730 y x
       have i₂ := eq574
       grind)
    | exact superpose eq574 eq730
    | exact resolve eq730 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq1717 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X3)) X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq103 X0 x x X0 X0 X3
       have i₂ := eq727 X0 (M.op (M.op x X0) (M.op x x))
       grind)
    | exact superpose eq727 eq103
    | exact resolve eq103 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq727
  have eq3198 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq730 (σ y) (σ x)
       have i₂ := eq896
       grind)
    | exact superpose eq896 eq730
    | exact resolve eq730 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq3203 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3198
       have i₂ := eq94 y
       grind)
    | exact superpose eq94 eq3198
    | exact resolve eq3198 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq3198
  have eq3321 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq3203
       grind)
    | exact superpose eq3203 eq10
    | exact resolve eq10 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3203
  have eq3369 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3321
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq3321
    | exact resolve eq3321 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3321
  have eq3370 : y = (M.op y y) := by grind
  clear eq3369
  have eq3464 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq3370
       grind)
    | exact superpose eq3370 eq9
    | exact resolve eq9 eq3370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3503 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq167 y X0
       have i₂ := eq3370
       grind)
    | exact superpose eq3370 eq167
    | exact resolve eq167 eq3370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq3516 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq1717 y X0
       have i₂ := eq3370
       grind)
    | exact superpose eq3370 eq1717
    | exact resolve eq1717 eq3370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717 eq3370
  have eq3518 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq3516 X0
       have i₂ := eq730 y X0
       grind)
    | exact superpose eq730 eq3516
    | exact resolve eq3516 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730 eq3516
  have eq3753 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3464 X0
       have i₂ := eq3518 X0
       grind)
    | exact superpose eq3518 eq3464
    | exact resolve eq3464 eq3518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3464
  have eq3859 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq3518 X0
       have i₂ := eq3753 X0
       grind)
    | exact superpose eq3753 eq3518
    | exact resolve eq3518 eq3753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3518
  have eq3861 : ∀ X0 X1 : G, (M.op (M.op (M.op y X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 y X0
       have i₂ := eq3753 X0
       grind)
    | exact superpose eq3753 eq9
    | exact resolve eq9 eq3753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3987 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3861 X0 X1
       have i₂ := eq3753 X1
       grind)
    | exact superpose eq3753 eq3861
    | exact resolve eq3861 eq3753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3753 eq3861
  have eq8963 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3503 X0
       have i₂ := eq3987 X0 (σ y)
       grind)
    | exact superpose eq3987 eq3503
    | exact resolve eq3503 eq3987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3503
  have eq9053 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3987 X0 (σ y)
       have i₂ := eq8963 X0
       grind)
    | exact superpose eq8963 eq3987
    | exact resolve eq3987 eq8963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3987 eq8963
  have eq9838 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9053 (σ x)
       grind)
    | exact superpose eq9053 eq16
    | exact resolve eq16 eq9053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9053
  have eq9874 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq9838
       have i₂ := eq3859 x
       grind)
    | exact superpose eq3859 eq9838
    | exact resolve eq9838 eq3859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3859 eq9838
  have eq9875 : False := by grind
  exact eq9875

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pyx_y_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq55
    | (have j0 := eq55 (σ X0) (σ X1)
       grind)
    | exact resolve eq55 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq33 (τ X0)
       grind)
    | exact superpose eq33 eq18
    | exact resolve eq18 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq82 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81
    | exact resolve eq81 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq90 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq82
    | exact resolve eq82 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq82
  have eq94 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq90 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X4)) X5)) X0) = X0 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq23 X0 (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X4 X5
       have i₂ := eq23 X0 X1 X2 X3
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq141 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66 y x
       grind)
    | exact superpose eq66 eq16
    | (have j1 := eq66 y x
       grind)
    | exact resolve eq16 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq167 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq9
    | exact resolve eq9 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq106 (σ X0)
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq106
    | exact resolve eq106 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq319 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq206 X0
       grind)
    | exact superpose eq206 eq9
    | exact resolve eq9 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq570 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq141
       have i₂ := eq55 y x
       grind)
    | exact superpose eq55 eq141
    | (have j1 := eq55 (σ y) (σ x)
       grind)
    | exact resolve eq141 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq141
  have eq571 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq570
  have eq639 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (M.op (τ X0) (τ X0))) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq319 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq319
    | exact resolve eq319 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq654 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq639 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq639
    | exact resolve eq639 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq639
  have eq721 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq654 (M.op X1 X0) X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq654
    | exact resolve eq654 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq724 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq654 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq654
    | exact resolve eq654 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq889 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq724 y x
       have i₂ := eq571
       grind)
    | exact superpose eq571 eq724
    | exact resolve eq724 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq1706 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X3)) X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq103 X0 x x X0 X0 X3
       have i₂ := eq721 X0 (M.op (M.op x X0) (M.op x x))
       grind)
    | exact superpose eq721 eq103
    | exact resolve eq103 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq721
  have eq3187 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq724 (σ y) (σ x)
       have i₂ := eq889
       grind)
    | exact superpose eq889 eq724
    | exact resolve eq724 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq3192 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3187
       have i₂ := eq94 y
       grind)
    | exact superpose eq94 eq3187
    | exact resolve eq3187 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq3187
  have eq3309 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq3192
       grind)
    | exact superpose eq3192 eq10
    | exact resolve eq10 eq3192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3192
  have eq3357 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3309
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq3309
    | exact resolve eq3309 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3309
  have eq3358 : y = (M.op y y) := by grind
  clear eq3357
  have eq3452 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq3358
       grind)
    | exact superpose eq3358 eq9
    | exact resolve eq9 eq3358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3491 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq167 y X0
       have i₂ := eq3358
       grind)
    | exact superpose eq3358 eq167
    | exact resolve eq167 eq3358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq3504 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq1706 y X0
       have i₂ := eq3358
       grind)
    | exact superpose eq3358 eq1706
    | exact resolve eq1706 eq3358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1706 eq3358
  have eq3506 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq3504 X0
       have i₂ := eq724 y X0
       grind)
    | exact superpose eq724 eq3504
    | exact resolve eq3504 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724 eq3504
  have eq3766 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3452 X0
       have i₂ := eq3506 X0
       grind)
    | exact superpose eq3506 eq3452
    | exact resolve eq3452 eq3506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3452
  have eq3813 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq3506 X0
       have i₂ := eq3766 X0
       grind)
    | exact superpose eq3766 eq3506
    | exact resolve eq3506 eq3766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3506
  have eq3815 : ∀ X0 X1 : G, (M.op (M.op (M.op y X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 y X0
       have i₂ := eq3766 X0
       grind)
    | exact superpose eq3766 eq9
    | exact resolve eq9 eq3766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3940 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3815 X0 X1
       have i₂ := eq3766 X1
       grind)
    | exact superpose eq3766 eq3815
    | exact resolve eq3815 eq3766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3766 eq3815
  have eq8908 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3491 X0
       have i₂ := eq3940 X0 (σ y)
       grind)
    | exact superpose eq3940 eq3491
    | exact resolve eq3491 eq3940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3491
  have eq8998 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3940 X0 (σ y)
       have i₂ := eq8908 X0
       grind)
    | exact superpose eq8908 eq3940
    | exact resolve eq3940 eq8908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3940 eq8908
  have eq9778 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8998 (σ x)
       grind)
    | exact superpose eq8998 eq16
    | exact resolve eq16 eq8998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8998
  have eq9814 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq9778
       have i₂ := eq3813 x
       grind)
    | exact superpose eq3813 eq9778
    | exact resolve eq9778 eq3813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3813 eq9778
  have eq9815 : False := by grind
  exact eq9815

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,Y) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_x_pyy_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  clear eq23
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq64 (σ X0)
       grind)
    | exact superpose eq64 eq15
    | exact resolve eq15 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq64 (τ X0)
       grind)
    | exact superpose eq64 eq19
    | exact resolve eq19 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq74 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq71
    | exact resolve eq71 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq67
    | exact resolve eq67 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq82 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq74 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq74
    | exact resolve eq74 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq74
  have eq89 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq9
    | exact resolve eq9 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ X0)
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq12
    | exact resolve eq12 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq10
    | exact resolve eq10 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq199 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq207 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq199 X0
       grind)
    | exact superpose eq199 eq9
    | exact resolve eq9 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq258 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq207 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq207
    | exact resolve eq207 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq207 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq89 X0 (σ X0)
       grind)
    | exact superpose eq89 eq207
    | exact resolve eq207 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq207
  have eq348 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq353 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq348 X0 X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq348
    | (have j0 := eq348 X0 X1
       grind)
    | exact resolve eq348 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq359 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq353 X0 X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq353
    | (have j0 := eq353 X0 X1
       grind)
    | exact resolve eq353 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq923 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (M.op (σ X1) (σ X1))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq359 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq359
    | (have j0 := eq359 (σ X1) (σ X0)
       grind)
    | exact resolve eq359 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq969 : ∀ X0 X1 : G, (σ (σ X0)) = (σ (σ (M.op X1 X1))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq923 X0 X1
       have i₂ := eq78 X1
       grind)
    | exact superpose eq78 eq923
    | (have j0 := eq923 X0 X1
       grind)
    | exact resolve eq923 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq986 : ∀ X0 X1 : G, (σ (σ (M.op X1 X1))) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ X0)) = (σ (σ (M.op X1 X1))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq969 X0 X1
       have i₂ := eq78 X1
       grind)
    | exact superpose eq78 eq969
    | (have j0 := eq969 X0 X1
       grind)
    | exact resolve eq969 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq36470 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (M.op (σ X0) (σ X0))) = (k (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ (M.op X0 X0))) = (σ (σ X1)) ∨ (σ (σ (k X1 X0))) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (σ X0) (σ (σ X1))
       have i₂ := eq986 X1 X0
       grind)
    | exact superpose eq986 eq91
    | (have j0 := eq91 (σ X0) (σ (σ X1))
       have j1 := eq986 X1 X0
       grind)
    | exact resolve eq91 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq36672 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (σ (σ (k X1 X0))) ∨ (σ (σ (M.op X0 X0))) = (σ (σ X1)) ∨ (σ (σ (k X1 X0))) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq986 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq36835 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (M.op (σ X0) (σ X0))) = (k (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ (M.op X0 X0))) = (σ (σ X1)) ∨ (σ (σ (k X1 X0))) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq36470 X0 X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq36470
    | (have j0 := eq36470 X0 X1
       grind)
    | exact resolve eq36470 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36470
  have eq36836 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) = (k (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ (M.op X0 X0))) = (σ (σ X1)) ∨ (σ (σ (k X1 X0))) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq36835 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36835
  have eq37095 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) = (σ (k (σ X1) (σ X0))) ∨ (σ (σ (M.op X0 X0))) = (σ (σ X1)) ∨ (σ (σ (k X1 X0))) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq36836 X0 X1
       have i₂ := eq15 (σ X1) (σ X0)
       grind)
    | exact superpose eq15 eq36836
    | (have j0 := eq36836 X0 X1
       grind)
    | exact resolve eq36836 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36836
  have eq37228 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) = (σ (σ (k X1 X0))) ∨ (σ (σ (M.op X0 X0))) = (σ (σ X1)) ∨ (σ (σ (k X1 X0))) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq37095 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq37095
    | (have j0 := eq37095 X0 X1
       grind)
    | exact resolve eq37095 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37095
  have eq37319 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (σ (σ (k X1 X0))) ∨ (σ (σ (M.op X0 X0))) = (σ (σ X1)) ∨ (σ (σ (k X1 X0))) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq37228 X0 X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq37228
    | (have j0 := eq37228 X0 X1
       grind)
    | exact resolve eq37228 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq37228
  have eq37352 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (σ (σ X1)) ∨ (σ (σ (k X1 X0))) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq37319 X0 X1
       have j1 := eq36672 X0 X1
       grind)
    | (have r₁ := eq37319 X0 X1
       have r₂ := eq36672 X0 X1
       grind)
    | (have r₁ := eq37319 X0 (k X1 X0)
       have r₂ := eq36672 X0 X1
       grind)
    | exact resolve eq37319 eq36672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36672 eq37319
  have eq37388 : ∀ X0 X1 : G, (σ (σ (k X1 X0))) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ (M.op X0 X0))) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq37352 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37352
  have eq52896 : ∀ X0 X1 : G, (σ (σ (k (τ X0) X1))) = (M.op (σ (σ X1)) (σ X0)) ∨ (σ X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq37388 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37388
    | exact resolve eq37388 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37388
  have eq53417 : ∀ X0 X1 : G, (σ (k X0 (σ X1))) = (M.op (σ (σ X1)) (σ X0)) ∨ (σ X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq52896 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq52896
    | (have j0 := eq52896 X0 X1
       grind)
    | exact resolve eq52896 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq52896
  have eq53819 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (σ (M.op (τ X0) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq53417 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq53417
    | (have j0 := eq53417 X1 (τ X0)
       grind)
    | exact resolve eq53417 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53417
  have eq53998 : ∀ X0 X1 : G, (σ X1) = (σ (σ (τ (M.op X0 X0)))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53819 X0 X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq53819
    | (have j0 := eq53819 X0 X1
       grind)
    | exact resolve eq53819 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53819
  have eq54008 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq53998 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq53998
    | (have j0 := eq53998 X0 X1
       grind)
    | exact resolve eq53998 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53998
  have eq54032 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq54008 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq54008
    | (have j0 := eq54008 (τ X1) (τ X0)
       grind)
    | exact resolve eq54008 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq54220 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq54032 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq54032
    | (have j0 := eq54032 X0 X1
       grind)
    | exact resolve eq54032 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54032
  have eq54242 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq54220 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq54220
    | (have j0 := eq54220 X0 X1
       grind)
    | exact resolve eq54220 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54220
  have eq54249 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq54242 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq54242
    | (have j0 := eq54242 X0 X1
       grind)
    | exact resolve eq54242 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54242
  have eq54254 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X1 X1))) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq54249 X0 X1
       have i₂ := eq102 X1
       grind)
    | exact superpose eq102 eq54249
    | (have j0 := eq54249 X0 X1
       grind)
    | exact resolve eq54249 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq54249
  have eq54259 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq54254 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq54254
    | (have j0 := eq54254 X0 X1
       grind)
    | exact resolve eq54254 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54254
  have eq54262 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq54259 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq54259
    | (have j0 := eq54259 X0 X1
       grind)
    | exact resolve eq54259 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54259
  have eq54295 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq54008 X0 X1
       have i₂ := eq54262 X1 X0
       grind)
    | exact superpose eq54262 eq54008
    | (have j0 := eq54008 X0 X1
       have j1 := eq54262 X1 X0
       grind)
    | exact resolve eq54008 eq54262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54008 eq54262
  have eq54573 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq54295 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54295
  have eq55071 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq54573 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54573
  have eq55225 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq55071 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55071
  have eq56789 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq55225 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55225
  have eq56883 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq56789 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56789
  have eq57145 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq56883 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56883
  have eq57227 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq57145 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57145
  have eq58243 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq57227 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57227
  have eq58519 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq58243 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58243
  have eq58898 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq58519 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58519
  have eq59475 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq58898 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58898
  have eq59804 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq59475 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59475
  have eq61762 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq59804 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59804
  have eq62274 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq61762 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61762
  have eq62541 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq62274 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62274
  have eq63769 : ∀ X0 X2 : G, (σ X2) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X2)) = (σ (M.op X0 X2)) ∨ (M.op X0 X0) = X2 := by
    intro X0 X2
    first
    | (have j0 := eq62541 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62541
  have eq64782 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq63769 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63769
  have eq64987 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq64782 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64782
  have eq65242 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq64987 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64987
  have eq65518 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq65242 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65242
  have eq65682 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq65518 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65518
  have eq66312 : ∀ X0 X3 : G, (σ (M.op X0 X0)) = (σ X3) ∨ (M.op (σ X0) (σ X3)) = (σ (M.op X0 X3)) ∨ (M.op X0 X0) = X3 := by
    intro X0 X3
    first
    | (have j0 := eq65682 X0 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65682
  have eq66976 : ∀ X0 X2 : G, (σ X2) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X2)) = (σ (M.op X0 X2)) ∨ (M.op X0 X0) = X2 := by
    intro X0 X2
    first
    | (have j0 := eq66312 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66312
  have eq67096 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq66976 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66976
  have eq68339 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq67096 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67096
  have eq68582 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq68339 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68339
  have eq69021 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq68582 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68582
  have eq69276 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq69021 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69021
  have eq69546 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq69276 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69276
  have eq70150 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq69546 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69546
  have eq70362 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq70150 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70150
  have eq72250 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq70362 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70362
  have eq72610 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq72250 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72250
  have eq73737 : ∀ X0 X2 : G, (σ X2) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X2)) = (σ (M.op X0 X2)) ∨ (M.op X0 X0) = X2 := by
    intro X0 X2
    first
    | (have j0 := eq72610 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72610
  have eq74404 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq73737 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73737
  have eq74771 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq74404 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74404
  have eq75126 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq74771 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74771
  have eq75371 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq75126 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75126
  have eq75624 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq75371 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75371
  have eq75898 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq75624 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75624
  have eq76227 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq75898 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75898
  have eq76648 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq76227 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76227
  have eq77076 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq76648 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76648
  have eq78759 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq77076 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77076
  have eq79630 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq78759 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78759
  have eq84202 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq79630 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79630
  have eq84469 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq84202 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84202
  have eq84729 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq84469 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84469
  have eq86137 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq84729 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84729
  have eq87524 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq86137 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86137
  have eq88590 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq87524 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87524
  have eq131466 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq88590 x y
       grind)
    | exact superpose eq88590 eq16
    | (have j1 := eq88590 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq88590 x y
       grind)
    | exact resolve eq16 eq88590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88590
  have eq131883 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq131466
  have eq132604 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq131883
       grind)
    | exact superpose eq131883 eq10
    | exact resolve eq10 eq131883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131883
  have eq132890 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq132604
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq132604
    | exact resolve eq132604 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132604
  have eq132891 : y = (M.op x x) := by grind
  clear eq132890
  have eq133347 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq260 x
       have i₂ := eq132891
       grind)
    | exact superpose eq132891 eq260
    | exact resolve eq260 eq132891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq133587 : y = (M.op x y) := by
    first
    | (have i₁ := eq258 x x
       have i₂ := eq132891
       grind)
    | exact superpose eq132891 eq258
    | exact resolve eq258 eq132891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258 eq132891
  have eq133744 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq133587
       grind)
    | exact superpose eq133587 eq16
    | exact resolve eq16 eq133587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133587
  have eq133842 : False := by grind
  exact eq133842

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pyx_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq90 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq90 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq13 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq332 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq304 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq333 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq332 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq337 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq333 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq333 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq333 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq346 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq337 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq337
    | (have j0 := eq337 X0 X1
       grind)
    | exact resolve eq337 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq347 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq346 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq352 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq347 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq347
    | exact resolve eq347 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq347 x y
       grind)
    | exact superpose eq347 eq16
    | exact resolve eq16 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq473 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq352 X0 (τ X1)
       grind)
    | exact superpose eq352 eq17
    | exact resolve eq17 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq352
  have eq489 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq473 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq473
    | exact resolve eq473 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq496 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq489 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq489
    | exact resolve eq489 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq606 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq363
       have i₂ := eq496 x y
       grind)
    | exact superpose eq496 eq363
    | exact resolve eq363 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363 eq496
  have eq607 : False := by grind
  exact eq607

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_x_pyx_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq73
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq175 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | (have r₁ := eq13 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have r₂ := eq16 X0 X1 X2
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq183 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq186 : ∀ X0 : G, y ≠ y ∨ y = (k y (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq175 eq13
    | (have r₁ := eq13 y (M.op (M.op x y) (M.op x X0))
       have r₂ := eq175 X0
       grind)
    | exact resolve eq13 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq189 : ∀ X0 : G, y = (k y (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | (have j0 := eq186 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq218 : ∀ X0 : G, (σ y) = (k (σ y) (σ (M.op (M.op x y) (M.op x X0)))) := by
    intro X0
    first
    | exact superpose eq189 eq37
    | exact resolve eq37 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq219 : ∀ X0 : G, (σ y) = (k (σ y) (σ (M.op (M.op x y) (M.op x X0)))) := by
    intro X0
    first
    | (have i₁ := eq218 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq218
    | (have j0 := eq218 X0
       grind)
    | exact resolve eq218 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq597 : (M.op x y) = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq625 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq28 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq636 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq597
       grind)
    | exact superpose eq597 eq40
    | exact resolve eq40 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq597
  have eq637 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq636
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq636
    | exact resolve eq636 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq639 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq637
    | exact resolve eq637 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq648 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq639 eq610
    | exact resolve eq610 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610 eq639
  have eq655 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq648
       have r₂ := eq27
       grind)
    | exact resolve eq648 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq663 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq655 eq16
    | exact resolve eq16 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq752 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq655 eq663
    | exact resolve eq663 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq758 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op (σ y) X0) (σ y))) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq663 eq13
    | (have r₁ := eq13 X0 (M.op (M.op (σ y) X0) (σ y))
       have r₂ := eq663 X0
       grind)
    | exact resolve eq13 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq761 : ∀ X0 : G, (k X0 (M.op (M.op (σ y) X0) (σ y))) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq758 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq762 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq752
  have eq804 : (τ (σ y)) = (k y (τ (M.op (M.op (σ y) (σ y)) (σ y)))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq761 eq108
    | exact resolve eq108 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq761
  have eq806 : y = (k y (τ (M.op (M.op (σ y) (σ y)) (σ y)))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq804
    | exact resolve eq804 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq1250 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq177 X0 x x X0
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq2685 : y ≠ (τ (M.op (M.op (σ y) (σ y)) (σ y))) ∨ (τ (M.op (M.op (σ y) (σ y)) (σ y))) = (M.op y (τ (M.op (M.op (σ y) (σ y)) (σ y)))) ∨ y = (k (τ (M.op (M.op (σ y) (σ y)) (σ y))) y) ∨ y = (M.op y (τ (M.op (M.op (σ y) (σ y)) (σ y)))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq806 eq625
    | (have j0 := eq625 y (τ (M.op (M.op (σ y) (σ y)) (σ y)))
       grind)
    | exact resolve eq625 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625 eq806
  have eq2749 : y ≠ (τ (σ y)) ∨ (τ (M.op (M.op (σ y) (σ y)) (σ y))) = (M.op y (τ (M.op (M.op (σ y) (σ y)) (σ y)))) ∨ y = (k (τ (M.op (M.op (σ y) (σ y)) (σ y))) y) ∨ y = (M.op y (τ (M.op (M.op (σ y) (σ y)) (σ y)))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2685
       have i₂ := eq1250 sF3
       grind)
    | exact superpose eq1250 eq2685
    | exact resolve eq2685 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2685
  have eq2760 : (τ (M.op (M.op (σ y) (σ y)) (σ y))) = (M.op y (τ (M.op (M.op (σ y) (σ y)) (σ y)))) ∨ y = (k (τ (M.op (M.op (σ y) (σ y)) (σ y))) y) ∨ y = (M.op y (τ (M.op (M.op (σ y) (σ y)) (σ y)))) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq2749
       have r₂ := eq32
       grind)
    | exact resolve eq2749 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2749
  have eq2767 : (τ (σ y)) = (M.op y (τ (σ y))) ∨ y = (k (τ (M.op (M.op (σ y) (σ y)) (σ y))) y) ∨ y = (M.op y (τ (M.op (M.op (σ y) (σ y)) (σ y)))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2760
       have i₂ := eq1250 sF3
       grind)
    | exact superpose eq1250 eq2760
    | exact resolve eq2760 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2760
  have eq2771 : y = (M.op y y) ∨ y = (k (τ (M.op (M.op (σ y) (σ y)) (σ y))) y) ∨ y = (M.op y (τ (M.op (M.op (σ y) (σ y)) (σ y)))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq2767
    | exact resolve eq2767 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2767
  have eq2773 : y = (k (τ (σ y)) y) ∨ y = (M.op y y) ∨ y = (M.op y (τ (M.op (M.op (σ y) (σ y)) (σ y)))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2771
       have i₂ := eq1250 sF3
       grind)
    | exact superpose eq1250 eq2771
    | exact resolve eq2771 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2771
  have eq2776 : y = (k y y) ∨ y = (M.op y y) ∨ y = (M.op y (τ (M.op (M.op (σ y) (σ y)) (σ y)))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq2773
    | exact resolve eq2773 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2773
  have eq2778 : y = (M.op y y) ∨ y = (M.op y (τ (M.op (M.op (σ y) (σ y)) (σ y)))) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq620 y
       grind)
    | (have r₁ := eq2776
       have r₂ := eq620 y
       grind)
    | exact resolve eq2776 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2776
  have eq2780 : y = (M.op y (τ (σ y))) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2778
       have i₂ := eq1250 sF3
       grind)
    | exact superpose eq1250 eq2778
    | exact resolve eq2778 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2778
  have eq2782 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq2780
    | exact resolve eq2780 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2780
  have eq2783 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq2782
  have eq2801 : y ≠ y ∨ y = (k y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq2783
       grind)
    | exact superpose eq2783 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq2783
       grind)
    | exact resolve eq13 eq2783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2814 : y = (k y y) ∨ y = (M.op y x) := by grind
  clear eq2801
  have eq2816 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq2814
       grind)
    | exact superpose eq2814 eq41
    | exact resolve eq41 eq2814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq2814
  have eq2821 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2816
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2816
    | exact resolve eq2816 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2816
  have eq2826 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2821 eq620
    | (have j0 := eq620 (σ y)
       grind)
    | (have r₁ := eq620 (σ y)
       have r₂ := eq2821
       grind)
    | exact resolve eq620 eq2821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2821
  have eq2829 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq2826
  have eq2834 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2829 eq762
    | exact resolve eq762 eq2829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762 eq2829
  have eq2876 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq2834
  have eq2921 : (σ x) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2876 eq655
    | exact resolve eq655 eq2876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655 eq2876
  have eq2952 : y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq2921
  have eq2979 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq2952
       grind)
    | exact superpose eq2952 eq16
    | exact resolve eq16 eq2952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2987 : ∀ X0 : G, (k X0 (M.op (M.op y X0) y)) = X0 ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq184 X0 y x
       have i₂ := eq2952
       grind)
    | exact superpose eq2952 eq184
    | exact resolve eq184 eq2952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq3361 : x = (M.op (M.op y y) x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2979 x
       have i₂ := eq2952
       grind)
    | exact superpose eq2952 eq2979
    | exact resolve eq2979 eq2952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2979
  have eq3385 : x = (M.op (M.op y y) x) ∨ (σ x) = (σ y) := by grind
  clear eq3361
  have eq3509 : (σ y) = (k (σ y) (σ (M.op (M.op y y) y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq37 (M.op (M.op y y) y)
       have i₂ := eq2987 y
       grind)
    | exact superpose eq2987 eq37
    | exact resolve eq37 eq2987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2987
  have eq3521 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3509
       have i₂ := eq1250 y
       grind)
    | exact superpose eq1250 eq3509
    | exact resolve eq3509 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3509
  have eq3525 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3521
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3521
    | exact resolve eq3521 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3521
  have eq3529 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3525 eq153
    | exact resolve eq153 eq3525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq3525
  have eq3534 : y = (k y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq32 eq3529
    | exact resolve eq3529 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3529
  have eq3580 : y ≠ y ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq620 y
       have i₂ := eq3534
       grind)
    | exact superpose eq3534 eq620
    | (have j0 := eq620 y
       grind)
    | (have r₁ := eq620 y
       have r₂ := eq3534
       grind)
    | exact resolve eq620 eq3534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620 eq3534
  have eq3583 : y = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq3580
  have eq3593 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3385
       have i₂ := eq3583
       grind)
    | exact superpose eq3583 eq3385
    | exact resolve eq3385 eq3583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3385 eq3583
  have eq3632 : x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq3593
  have eq3689 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2952
       have i₂ := eq3632
       grind)
    | exact superpose eq3632 eq2952
    | exact resolve eq2952 eq3632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2952 eq3632
  have eq3726 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq3689
  have eq3912 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq3726 eq32
    | exact resolve eq32 eq3726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq3726
  have eq3995 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq3912
    | exact resolve eq3912 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3912
  have eq3996 : x = y := by grind
  clear eq3995
  have eq3999 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3996
       grind)
    | exact superpose eq3996 eq18
    | exact resolve eq18 eq3996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4000 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3996
       grind)
    | exact superpose eq3996 eq24
    | exact resolve eq24 eq3996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq4001 : ∀ X0 : G, (σ (k x X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq3996
       grind)
    | exact superpose eq3996 eq37
    | exact resolve eq37 eq3996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq4047 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2783
       have i₂ := eq3996
       grind)
    | exact superpose eq3996 eq2783
    | exact resolve eq2783 eq3996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2783 eq3996
  have eq4066 : x = (M.op x x) := by grind
  clear eq4047
  have eq4099 : ∀ X0 : G, (k (σ x) (σ X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4001 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq4001
    | exact resolve eq4001 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq4001
  have eq4100 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4000
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4000
    | exact resolve eq4000 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4000
  have eq4115 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4100 eq26
    | exact resolve eq26 eq4100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq4242 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq1250 x
       have i₂ := eq3999
       grind)
    | exact superpose eq3999 eq1250
    | exact resolve eq1250 eq3999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250
  have eq4271 : x = (M.op x y) := by
    first
    | (have i₁ := eq3999
       have i₂ := eq4066
       grind)
    | exact superpose eq4066 eq3999
    | exact resolve eq3999 eq4066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3999
  have eq4276 : (σ y) = (k (σ y) (σ (M.op (M.op x y) x))) := by
    first
    | (have i₁ := eq219 x
       have i₂ := eq4066
       grind)
    | exact superpose eq4066 eq219
    | exact resolve eq219 eq4066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq4066
  have eq4299 : (σ y) = (k (σ x) (σ (M.op (M.op x y) x))) := by
    first
    | exact superpose eq4099 eq4276
    | exact resolve eq4276 eq4099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4099 eq4276
  have eq4302 : (σ y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4242 eq4299
    | exact resolve eq4299 eq4242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4242 eq4299
  have eq4305 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq4302
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4302
    | exact resolve eq4302 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4302
  have eq4307 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4100 eq4305
    | exact resolve eq4305 eq4100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4100 eq4305
  have eq4310 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq4271
       grind)
    | exact superpose eq4271 eq22
    | exact resolve eq22 eq4271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4271
  have eq4454 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4310 eq20
    | exact resolve eq20 eq4310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4310
  have eq4547 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4115 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq4115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4115
  have eq4561 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4307 eq4547
    | exact resolve eq4547 eq4307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4307 eq4547
  have eq4562 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4561
  have eq4574 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq4562 eq27
    | exact resolve eq27 eq4562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4562
  have eq4614 : False := by grind
  exact eq4614

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_x_pyx_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq73
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq183 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | (have r₁ := eq13 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have r₂ := eq16 X0 X1 X2
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq183 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq208 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op x X0) (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq178 eq13
    | (have r₁ := eq13 X0 (M.op (M.op x X0) (M.op x y))
       have r₂ := eq178 X0
       grind)
    | exact resolve eq13 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq211 : ∀ X0 : G, (k X0 (M.op (M.op x X0) (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq208 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq224 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x (M.op x y)) (M.op x y)))) := by
    first
    | exact superpose eq211 eq38
    | exact resolve eq38 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq211
  have eq225 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x (M.op x y)) (M.op x y)))) := by
    first
    | exact superpose eq20 eq224
    | exact resolve eq224 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq597 : (M.op x y) = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq636 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq597
       grind)
    | exact superpose eq597 eq40
    | exact resolve eq40 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq597
  have eq637 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq636
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq636
    | exact resolve eq636 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq639 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq637
    | exact resolve eq637 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq648 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq639 eq610
    | exact resolve eq610 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610 eq639
  have eq655 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq648
       have r₂ := eq27
       grind)
    | exact resolve eq648 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq663 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq655 eq16
    | exact resolve eq16 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq655 eq663
    | exact resolve eq663 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq719 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq709
  have eq878 : ∀ X0 : G, (k X0 (M.op (M.op (M.op (σ y) (σ y)) X0) (σ x))) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq719 eq184
    | exact resolve eq184 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq940 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq177 X0 x x X0
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq1167 : (τ (σ y)) = (k y (τ (M.op (M.op (M.op (σ y) (σ y)) (σ y)) (σ x)))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq878 eq108
    | exact resolve eq108 eq878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq878
  have eq1169 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ x)))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1167
       have i₂ := eq940 sF3
       grind)
    | exact superpose eq940 eq1167
    | exact resolve eq1167 eq940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq1177 : y = (k y (τ (M.op (σ y) (σ x)))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq1169
    | exact resolve eq1169 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq1179 : y = (k y (τ (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq655 eq1177
    | exact resolve eq1177 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177
  have eq1180 : y = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq1179
    | exact resolve eq1179 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179
  have eq1182 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq1180
       grind)
    | exact superpose eq1180 eq41
    | exact resolve eq41 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq1183 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq620 y
       have i₂ := eq1180
       grind)
    | exact superpose eq1180 eq620
    | (have j0 := eq620 y
       grind)
    | (have r₁ := eq620 y
       have r₂ := eq1180
       grind)
    | exact resolve eq620 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180
  have eq1184 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq1183
  have eq1185 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1182
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1182
    | exact resolve eq1182 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq1199 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1185 eq620
    | (have j0 := eq620 (σ y)
       grind)
    | (have r₁ := eq620 (σ y)
       have r₂ := eq1185
       grind)
    | exact resolve eq620 eq1185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq1200 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq1199
  have eq1205 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1200 eq719
    | exact resolve eq719 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719 eq1200
  have eq1238 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq1205
  have eq1256 : (σ x) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1238 eq655
    | exact resolve eq655 eq1238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655 eq1238
  have eq1277 : y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq1256
  have eq1291 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq1277
       grind)
    | exact superpose eq1277 eq16
    | exact resolve eq16 eq1277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1297 : ∀ X0 : G, (k X0 (M.op (M.op y X0) y)) = X0 ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq184 X0 y x
       have i₂ := eq1277
       grind)
    | exact superpose eq1277 eq184
    | exact resolve eq184 eq1277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq1463 : x = (M.op (M.op y y) x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1291 x
       have i₂ := eq1277
       grind)
    | exact superpose eq1277 eq1291
    | exact resolve eq1291 eq1277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291
  have eq1481 : x = (M.op (M.op y y) x) ∨ (σ x) = (σ y) := by grind
  clear eq1463
  have eq1558 : (σ y) = (k (σ y) (σ (M.op (M.op y y) y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq37 (M.op (M.op y y) y)
       have i₂ := eq1297 y
       grind)
    | exact superpose eq1297 eq37
    | exact resolve eq37 eq1297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq1297
  have eq1569 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1558
       have i₂ := eq940 y
       grind)
    | exact superpose eq940 eq1558
    | exact resolve eq1558 eq940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1558
  have eq1573 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1569
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1569
    | exact resolve eq1569 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569
  have eq1577 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1573 eq153
    | exact resolve eq153 eq1573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq1573
  have eq1580 : y = (k y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq32 eq1577
    | exact resolve eq1577 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1577
  have eq1609 : y ≠ y ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq620 y
       have i₂ := eq1580
       grind)
    | exact superpose eq1580 eq620
    | (have j0 := eq620 y
       grind)
    | (have r₁ := eq620 y
       have r₂ := eq1580
       grind)
    | exact resolve eq620 eq1580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620 eq1580
  have eq1610 : y = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq1609
  have eq1616 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1481
       have i₂ := eq1610
       grind)
    | exact superpose eq1610 eq1481
    | exact resolve eq1481 eq1610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1481 eq1610
  have eq1635 : x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq1616
  have eq1647 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1277
       have i₂ := eq1635
       grind)
    | exact superpose eq1635 eq1277
    | exact resolve eq1277 eq1635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277 eq1635
  have eq1669 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1647
  have eq1679 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1669 eq32
    | exact resolve eq32 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1669
  have eq1741 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq1679
    | exact resolve eq1679 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1679
  have eq1742 : x = y := by grind
  clear eq1741
  have eq1744 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1742
       grind)
    | exact superpose eq1742 eq18
    | exact resolve eq18 eq1742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1745 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1742
       grind)
    | exact superpose eq1742 eq24
    | exact resolve eq24 eq1742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1761 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1184
       have i₂ := eq1742
       grind)
    | exact superpose eq1742 eq1184
    | exact resolve eq1184 eq1742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184 eq1742
  have eq1778 : x = (M.op x x) := by grind
  clear eq1761
  have eq1784 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1745
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1745
    | exact resolve eq1745 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1745
  have eq1786 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1784 eq26
    | exact resolve eq26 eq1784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1784
  have eq1894 : x = (M.op x y) := by
    first
    | (have i₁ := eq1744
       have i₂ := eq1778
       grind)
    | exact superpose eq1778 eq1744
    | exact resolve eq1744 eq1778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1744 eq1778
  have eq1919 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq1894
       grind)
    | exact superpose eq1894 eq22
    | exact resolve eq22 eq1894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1996 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1919 eq20
    | exact resolve eq20 eq1919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1919
  have eq2040 : (σ x) = (k (σ x) (σ (M.op (M.op x (M.op x y)) (M.op x y)))) := by
    first
    | exact superpose eq1996 eq225
    | exact resolve eq225 eq1996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq2065 : (σ x) = (k (σ x) (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)))) := by
    first
    | (have i₁ := eq2040
       have i₂ := eq1894
       grind)
    | exact superpose eq1894 eq2040
    | exact resolve eq2040 eq1894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894 eq2040
  have eq2085 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2065
       have i₂ := eq940 sF0
       grind)
    | exact superpose eq940 eq2065
    | exact resolve eq2065 eq940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940 eq2065
  have eq2104 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq2085
    | exact resolve eq2085 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2085
  have eq2118 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1996 eq2104
    | exact resolve eq2104 eq1996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2104
  have eq2148 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1786 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq1786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1786
  have eq2155 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2118 eq2148
    | exact resolve eq2148 eq2118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2118 eq2148
  have eq2156 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2155
  have eq2162 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq2156 eq27
    | exact resolve eq27 eq2156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2156
  have eq2191 : False := by grind
  exact eq2191

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_x_pyx_y_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq17
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq63 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq65 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq108 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq9
    | exact resolve eq9 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq12
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq108 X0
       grind)
    | exact resolve eq12 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X0 X0) X0 X2
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq61
    | exact resolve eq61 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq133 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq123 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq211 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq122 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq122
    | exact resolve eq122 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq211 X0 X1
       grind)
    | exact superpose eq211 eq12
    | (have r₁ := eq12 (M.op X0 X1) X0
       have r₂ := eq211 X0 X1
       grind)
    | exact resolve eq12 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq239 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq261 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (k (τ (M.op (σ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op (σ X0) X1) X0
       have i₂ := eq252 (σ X0) X1
       grind)
    | exact superpose eq252 eq22
    | exact resolve eq22 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq252
  have eq278 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq278 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq278
    | (have j0 := eq278 (σ X0) (σ X1)
       grind)
    | exact resolve eq278 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1044 : ∀ X0 X1 X2 : G, (k X1 (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X1 (M.op X0 X0) X0 X2
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq65
    | exact resolve eq65 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq108
  have eq1533 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq126 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq126
    | exact resolve eq126 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq1735 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq289 X1 X0
       have i₂ := eq278 X1 X0
       grind)
    | exact superpose eq278 eq289
    | (have j0 := eq289 X1 X0
       have j1 := eq278 (σ X1) (σ X0)
       grind)
    | exact resolve eq289 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1850 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1044 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq1044
    | exact resolve eq1044 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq21595 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1735 x y
       grind)
    | exact superpose eq1735 eq16
    | (have j1 := eq1735 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1735 x y
       grind)
    | exact resolve eq16 eq1735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1735
  have eq21828 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq21595
  have eq21848 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq261 y (σ x)
       have i₂ := eq21828
       grind)
    | exact superpose eq21828 eq261
    | exact resolve eq261 eq21828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq22070 : y = (k y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq21848
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq21848
    | exact resolve eq21848 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21848
  have eq22095 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq278 y y
       have i₂ := eq22070
       grind)
    | exact superpose eq22070 eq278
    | (have j0 := eq278 y y
       grind)
    | exact resolve eq278 eq22070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq22070
  have eq22096 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq22095
  have eq22112 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq122 y X0
       have i₂ := eq22096
       grind)
    | exact superpose eq22096 eq122
    | exact resolve eq122 eq22096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22264 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1533 y y x
       have i₂ := eq22096
       grind)
    | exact superpose eq22096 eq1533
    | exact resolve eq1533 eq22096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22096
  have eq22328 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq22264 X0
       have i₂ := eq211 y X0
       grind)
    | exact superpose eq211 eq22264
    | exact resolve eq22264 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22264
  have eq25496 : ∀ X0 : G, y = (M.op y x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq22328 eq22112
    | exact resolve eq22112 eq22328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22112 eq22328
  have eq25549 : ∀ X0 : G, y = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq211 y x
       have i₂ := eq25496 X0
       grind)
    | exact superpose eq25496 eq211
    | (have j1 := eq25496 y
       grind)
    | exact resolve eq211 eq25496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25496
  have eq26177 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have j0 := eq25549 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25549
  have eq26178 : y = (M.op y y) := by grind
  clear eq26177
  have eq26250 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq122 y X0
       have i₂ := eq26178
       grind)
    | exact superpose eq26178 eq122
    | exact resolve eq122 eq26178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq26257 : y = (k y y) := by
    first
    | (have i₁ := eq133 y
       have i₂ := eq26178
       grind)
    | exact superpose eq26178 eq133
    | exact resolve eq133 eq26178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq26402 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq1533 y y x
       have i₂ := eq26178
       grind)
    | exact superpose eq26178 eq1533
    | exact resolve eq1533 eq26178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533
  have eq26407 : ∀ X0 : G, y = (k y (M.op y (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq1850 y y x
       have i₂ := eq26178
       grind)
    | exact superpose eq26178 eq1850
    | exact resolve eq1850 eq26178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850 eq26178
  have eq26467 : ∀ X0 : G, y = (k y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq26407 X0
       have i₂ := eq211 y X0
       grind)
    | exact superpose eq211 eq26407
    | exact resolve eq26407 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26407
  have eq26469 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq26402 X0
       have i₂ := eq211 y X0
       grind)
    | exact superpose eq211 eq26402
    | exact resolve eq26402 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq26402
  have eq26537 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq289 y y
       have i₂ := eq26257
       grind)
    | exact superpose eq26257 eq289
    | (have j0 := eq289 y y
       grind)
    | exact resolve eq289 eq26257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq26257
  have eq26540 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq26537
  have eq27412 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq26250 X0
       have i₂ := eq26469 X0
       grind)
    | exact superpose eq26469 eq26250
    | exact resolve eq26250 eq26469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26250
  have eq27413 : (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq21828
       have i₂ := eq27412 x
       grind)
    | exact superpose eq27412 eq21828
    | exact resolve eq21828 eq27412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21828
  have eq27417 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq26469 X0
       have i₂ := eq27412 X0
       grind)
    | exact superpose eq27412 eq26469
    | exact resolve eq26469 eq27412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26469
  have eq27418 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq26467 X0
       have i₂ := eq27412 X0
       grind)
    | exact superpose eq27412 eq26467
    | exact resolve eq26467 eq27412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26467 eq27412
  have eq27979 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq27417 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27417
  have eq27980 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have j0 := eq27418 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27418
  have eq28096 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27979 x
       grind)
    | exact superpose eq27979 eq16
    | exact resolve eq16 eq27979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27979
  have eq31144 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq27413
       grind)
    | exact superpose eq27413 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq27413
       grind)
    | exact resolve eq13 eq27413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31245 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq31144
  have eq31325 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq31245
       have r₂ := eq28096
       grind)
    | exact resolve eq31245 eq28096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31245
  have eq31376 : (σ x) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq31325
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq31325
    | exact resolve eq31325 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31325
  have eq31404 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq31376
       have i₂ := eq27980 x
       grind)
    | exact superpose eq27980 eq31376
    | exact resolve eq31376 eq27980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27980 eq31376
  have eq31464 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq31404 eq27413
    | exact resolve eq27413 eq31404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27413
  have eq31466 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq28096
       have i₂ := eq31404
       grind)
    | exact superpose eq31404 eq28096
    | exact resolve eq28096 eq31404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31404
  have eq31553 : x = y := by
    first
    | (have r₁ := eq31464
       have r₂ := eq31466
       grind)
    | exact resolve eq31464 eq31466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31464 eq31466
  have eq31591 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26540
       have i₂ := eq31553
       grind)
    | exact superpose eq31553 eq26540
    | exact resolve eq26540 eq31553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26540
  have eq31596 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq28096
       have i₂ := eq31553
       grind)
    | exact superpose eq31553 eq28096
    | exact resolve eq28096 eq31553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28096 eq31553
  have eq31605 : False := by grind
  exact eq31605

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then X else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_x_pyx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq60 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X1 X0) (M.op X1 X2))
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq62 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
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
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq75
    | exact resolve eq75 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq82
    | exact resolve eq82 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq84
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq84
    | exact resolve eq84 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq92 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq93 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq102 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq16
    | exact resolve eq16 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) ∨ (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) = (k (M.op (M.op X1 X0) (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) = (k (M.op (M.op X1 X0) (M.op X1 X2)) X0) ∨ (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq106 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq113 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq16
    | exact resolve eq16 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq160 : (σ (k (k x y) x)) = (k (k (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq39 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq39
    | exact resolve eq39 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq275 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq440 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq58 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq451 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq440 X0
       grind)
    | exact superpose eq440 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq440 X0
       grind)
    | exact resolve eq13 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq440 X0
       grind)
    | exact superpose eq440 eq14
    | exact resolve eq14 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq458 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq451 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq639 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq70 X0 X1
       grind)
    | exact superpose eq70 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq70 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq70 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq70 X0 X1
       grind)
    | exact resolve eq12 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq70 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq654 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq653 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq657 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq639 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq660 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq657 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq657 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq657 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq657 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq670 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq660 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq660
    | (have j0 := eq660 X0 X1
       grind)
    | exact resolve eq660 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq729 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq275 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq275
    | (have j0 := eq275 X0 x
       grind)
    | exact resolve eq275 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq759 : (k (k x y) x) = (τ (k (k (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq55 eq729
    | exact resolve eq729 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq789 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X1) X0)) = (k (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X1) X0) X1) ∨ (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X1) X0) = (M.op X1 (M.op (M.op (M.op (M.op (M.op (M.op X2 X3) (M.op X2 X4)) X0) X3) X1) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq107 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq107
    | exact resolve eq107 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq107
  have eq1409 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq453 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq453
    | exact resolve eq453 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1412 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq59 eq453
    | exact resolve eq453 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1415 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq60 eq453
    | exact resolve eq453 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq1465 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1415 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq1415
       grind)
    | exact resolve eq13 eq1415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415
  have eq1478 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq1465
  have eq1553 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X0
       have i₂ := eq1409 X0 X1
       grind)
    | exact superpose eq1409 eq13
    | (have j0 := eq13 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X1) X0
       have r₂ := eq1409 X0 X1
       grind)
    | exact resolve eq13 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1604 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq1553 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553
  have eq5580 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq654 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq654
    | (have j0 := eq654 (τ X0)
       grind)
    | exact resolve eq654 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq654
  have eq5588 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5580 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5580
    | (have j0 := eq5580 X0
       grind)
    | exact resolve eq5580 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5580
  have eq5594 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5588 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5588
    | (have j0 := eq5588 X0
       grind)
    | exact resolve eq5588 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5588
  have eq13487 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq85 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13488 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq13487
    | exact resolve eq13487 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13487
  have eq13499 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq13488
       have r₂ := eq27
       grind)
    | exact resolve eq13488 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13488
  have eq13502 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq13499
    | exact resolve eq13499 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13499
  have eq13505 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq13502 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq13502
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq13502
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq13502
       grind)
    | exact resolve eq13 eq13502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13502
  have eq13553 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq13505
  have eq13785 : (τ (σ x)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq13553 eq55
    | exact resolve eq55 eq13553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq13786 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq13553 eq85
    | exact resolve eq85 eq13553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq13553
  have eq13795 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13786
  have eq13803 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq13785
    | exact resolve eq13785 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13785
  have eq13807 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq13803
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13803
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq13803
       have r₂ := eq13 x y
       grind)
    | exact resolve eq13803 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13803
  have eq13809 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq13807
       grind)
    | exact superpose eq13807 eq44
    | exact resolve eq44 eq13807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq13813 : (σ (k x x)) = (k (k (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq160
       have i₂ := eq13807
       grind)
    | exact superpose eq13807 eq160
    | exact resolve eq160 eq13807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq13817 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq13807
       grind)
    | exact superpose eq13807 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq13807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13807
  have eq13818 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13817
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13817
    | exact resolve eq13817 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13817
  have eq13822 : (k (σ x) (σ x)) = (k (k (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13813
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq13813
    | exact resolve eq13813 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq13813
  have eq13826 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13809
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13809
    | exact resolve eq13809 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13809
  have eq13828 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13818
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13818
    | exact resolve eq13818 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13818
  have eq13829 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13828
  have eq14084 : (τ (k (σ x) (σ x))) = (k (k x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13826 eq759
    | exact resolve eq759 eq13826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq14088 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13826 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq13826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13826
  have eq14091 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq14088
    | exact resolve eq14088 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14088
  have eq14094 : (k x x) = (k (k x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq49 eq14084
    | exact resolve eq14084 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14084
  have eq14102 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq14091
    | exact resolve eq14091 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14091
  have eq14103 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14102
  have eq14823 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq13795
       grind)
    | exact superpose eq13795 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq13795
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq13795
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq13795
       grind)
    | exact resolve eq12 eq13795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13795
  have eq14877 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14823
  have eq14878 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14877
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14877
    | exact resolve eq14877 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14877
  have eq14879 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14878
  have eq14880 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14879
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14879
    | exact resolve eq14879 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14879
  have eq15695 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq92
       have i₂ := eq14880
       grind)
    | exact superpose eq14880 eq92
    | exact resolve eq92 eq14880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14880
  have eq15715 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq15695
    | exact resolve eq15695 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15695
  have eq19234 : (k (σ x) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13822
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq13822
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq13822 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13822
  have eq19246 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq19234
       have i₂ := eq1604 sF2 sF3
       grind)
    | exact superpose eq1604 eq19234
    | exact resolve eq19234 eq1604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19234
  have eq19248 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq19246
    | exact resolve eq19246 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19246
  have eq19249 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq19248
    | exact resolve eq19248 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19248
  have eq19250 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq19249
  have eq21425 : (k x x) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq14094
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq14094
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq14094 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14094
  have eq21446 : (M.op x y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq21425
       have i₂ := eq1604 x y
       grind)
    | exact superpose eq1604 eq21425
    | exact resolve eq21425 eq1604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21425
  have eq21455 : (M.op x y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq21446
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21446
    | exact resolve eq21446 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21446
  have eq21464 : y = (M.op x y) ∨ (M.op x y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq21455
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21455
    | exact resolve eq21455 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21455
  have eq21465 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq21464
  have eq28757 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq19250 eq5594
    | (have j0 := eq5594 (σ x)
       grind)
    | exact resolve eq5594 eq19250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19250
  have eq28784 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq28757
       have r₂ := eq14103
       grind)
    | exact resolve eq28757 eq14103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14103 eq28757
  have eq29092 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq5594 x
       have i₂ := eq21465
       grind)
    | exact superpose eq21465 eq5594
    | (have j0 := eq5594 x
       grind)
    | exact resolve eq5594 eq21465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5594 eq21465
  have eq29128 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq29092
       have r₂ := eq13829
       grind)
    | exact resolve eq29092 eq13829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13829 eq29092
  have eq32474 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) X0) = (k X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) ∨ (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq789 X0 (M.op (M.op (M.op (M.op X2 X0) (M.op X2 x)) X0) X2) X2 X0 x
       have i₂ := eq14 X0 (M.op (M.op (M.op X2 X0) (M.op X2 x)) X0) X2
       grind)
    | exact superpose eq14 eq789
    | exact resolve eq789 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq32504 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) X0) = (k X0 (M.op X0 X3)) ∨ (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq32474 X0 X1 X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq32474
    | (have j0 := eq32474 X0 X1 X2 X3
       grind)
    | exact resolve eq32474 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32474
  have eq32511 : ∀ X0 X3 : G, (M.op (M.op X0 X3) X0) = (k X0 (M.op X0 X3)) ∨ (M.op (M.op X0 X3) X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq32504 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq32504
    | (have j0 := eq32504 X0 x x X3
       grind)
    | exact resolve eq32504 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32504
  have eq32880 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq28784 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq28784
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq28784
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq28784
       grind)
    | exact resolve eq12 eq28784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28784
  have eq32941 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq32880
  have eq32942 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq32941
    | exact resolve eq32941 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32941
  have eq32943 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq32942
  have eq32944 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq32943
    | exact resolve eq32943 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32943
  have eq33572 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq29128
       grind)
    | exact superpose eq29128 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq29128
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq29128
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq29128
       grind)
    | exact resolve eq12 eq29128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29128
  have eq33633 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq33572
  have eq33634 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq33633
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq33633
    | exact resolve eq33633 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33633
  have eq33635 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq33634
  have eq33636 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq33635
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq33635
    | exact resolve eq33635 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33635
  have eq34156 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32944 eq15715
    | exact resolve eq15715 eq32944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15715 eq32944
  have eq34197 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq34156
  have eq34207 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq34197
       have r₂ := eq27
       grind)
    | exact resolve eq34197 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34197
  have eq34377 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34207 eq458
    | exact resolve eq458 eq34207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458 eq34207
  have eq34923 : (τ (σ x)) = (k x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34377 eq49
    | exact resolve eq49 eq34377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq34377
  have eq34986 : x = (k x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq34923
    | exact resolve eq34923 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq34923
  have eq35453 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq34986
       grind)
    | exact superpose eq34986 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq34986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34986
  have eq35480 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq35453
  have eq36733 : (σ x) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq670 y x
       have i₂ := eq33636
       grind)
    | exact superpose eq33636 eq670
    | (have j0 := eq670 y x
       grind)
    | exact resolve eq670 eq33636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33636
  have eq36746 : (σ x) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq36733
    | exact resolve eq36733 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36733
  have eq36766 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq36746
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36746
    | exact resolve eq36746 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36746
  have eq36780 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq36766
       have r₂ := eq35480
       grind)
    | exact resolve eq36766 eq35480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35480 eq36766
  have eq36793 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq36780
    | exact resolve eq36780 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36780
  have eq36806 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq36793
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36793
    | exact resolve eq36793 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36793
  have eq36819 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq36806
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36806
    | exact resolve eq36806 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36806
  have eq36831 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq36819
    | exact resolve eq36819 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36819
  have eq36847 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq36831
       have r₂ := eq27
       grind)
    | exact resolve eq36831 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36831
  have eq36861 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq36847
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36847
    | exact resolve eq36847 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36847
  have eq36863 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq36861
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36861
    | exact resolve eq36861 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36861
  have eq36866 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq36863
    | exact resolve eq36863 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36863
  have eq36867 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq36866
  have eq36868 : y = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq36867
       grind)
    | exact superpose eq36867 eq56
    | exact resolve eq56 eq36867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36869 : x = (M.op (M.op x (M.op x y)) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq59 x
       have i₂ := eq36867
       grind)
    | exact superpose eq36867 eq59
    | exact resolve eq59 eq36867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq36867
  have eq36997 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1412 eq36869
    | exact resolve eq36869 eq1412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36869
  have eq37604 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36997 eq36868
    | exact resolve eq36868 eq36997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36868 eq36997
  have eq37671 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq37604
  have eq37676 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37671
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq37671
    | exact resolve eq37671 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37671
  have eq37677 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq37676
  have eq37728 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37677 eq1478
    | exact resolve eq1478 eq37677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478 eq37677
  have eq37743 : (τ (σ y)) = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37728 eq102
    | exact resolve eq102 eq37728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq37728
  have eq37805 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq37743
    | exact resolve eq37743 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37743
  have eq37812 : y = (k y x) := by
    first
    | (have r₁ := eq37805
       have r₂ := eq50
       grind)
    | exact resolve eq37805 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq37805
  have eq37818 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq92
       have i₂ := eq37812
       grind)
    | exact superpose eq37812 eq92
    | exact resolve eq92 eq37812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq37833 : y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq37812
       grind)
    | exact superpose eq37812 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq37812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37867 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq37833
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq37833
    | exact resolve eq37833 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37833
  have eq37874 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq37818
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37818
    | exact resolve eq37818 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37818
  have eq37983 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37874 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq37874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38011 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq37983
    | exact resolve eq37983 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37983
  have eq41448 : ∀ X0 : G, x = (k x (M.op y (M.op y X0))) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq63 x y X0
       have i₂ := eq37867
       grind)
    | exact superpose eq37867 eq63
    | exact resolve eq63 eq37867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq41499 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1409 y x
       have i₂ := eq37867
       grind)
    | exact superpose eq37867 eq1409
    | exact resolve eq1409 eq37867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37867
  have eq41529 : ∀ X0 : G, x = (k x (M.op y X0)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq41448 X0
       have i₂ := eq1409 y X0
       grind)
    | exact superpose eq1409 eq41448
    | exact resolve eq41448 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41448
  have eq42069 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq38011 eq1604
    | exact resolve eq1604 eq38011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604 eq38011
  have eq43075 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq42069 eq113
    | exact resolve eq113 eq42069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq42069
  have eq43133 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq29 eq43075
    | exact resolve eq43075 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq43075
  have eq43435 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq43133 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq43133
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq43133
       grind)
    | exact resolve eq12 eq43133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43133
  have eq43498 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by grind
  clear eq43435
  have eq43500 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq26 eq43498
    | exact resolve eq43498 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43498
  have eq43501 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k y y) := by grind
  clear eq43500
  have eq43503 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq37874 eq43501
    | exact resolve eq43501 eq37874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37874 eq43501
  have eq43504 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq26 eq43503
    | exact resolve eq43503 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43503
  have eq43505 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq43504
  have eq43530 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq670 y y
       have i₂ := eq43505
       grind)
    | exact superpose eq43505 eq670
    | (have j0 := eq670 y y
       grind)
    | exact resolve eq670 eq43505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670 eq43505
  have eq43535 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq43530
  have eq43536 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq43535
  have eq43552 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43536
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43536
    | exact resolve eq43536 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43536
  have eq43689 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq43552 eq453
    | exact resolve eq453 eq43552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq43694 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq43552 eq14
    | exact resolve eq14 eq43552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43552
  have eq43779 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq43694 x
       have i₂ := eq1409 sF3 x
       grind)
    | exact superpose eq1409 eq43694
    | exact resolve eq43694 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409 eq43694
  have eq71073 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq43779 eq43689
    | exact resolve eq43689 eq43779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43689
  have eq71194 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq71073 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71073
  have eq71388 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq71194 eq43779
    | exact resolve eq43779 eq71194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43779 eq71194
  have eq71565 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq71388 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71388
  have eq72167 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq71565 eq26
    | (have j1 := eq71565 (σ x)
       grind)
    | exact resolve eq26 eq71565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq71565
  have eq72220 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq72167
  have eq72235 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq72220 eq27
    | exact resolve eq27 eq72220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq72220
  have eq177042 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq41529 y
       have i₂ := eq41499
       grind)
    | exact superpose eq41499 eq41529
    | exact resolve eq41529 eq41499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41499 eq41529
  have eq177063 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq177042
  have eq177078 : x = (k x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq177063
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq177063
       have r₂ := eq13 x y
       grind)
    | exact resolve eq177063 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177063
  have eq177131 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq177078
       grind)
    | exact superpose eq177078 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq177078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177078
  have eq177161 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq177131
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177131
    | exact resolve eq177131 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177131
  have eq177189 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq177161
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177161
    | exact resolve eq177161 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177161
  have eq177190 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq177189
  have eq179527 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32511 y x
       have i₂ := eq177190
       grind)
    | exact superpose eq177190 eq32511
    | exact resolve eq32511 eq177190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32511 eq177190
  have eq179531 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq179527
       have i₂ := eq37812
       grind)
    | exact superpose eq37812 eq179527
    | exact resolve eq179527 eq37812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37812 eq179527
  have eq179532 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq179531
  have eq179536 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq179532
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq179532
    | exact resolve eq179532 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179532
  have eq179537 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq179536
  have eq179541 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq179537 eq20
    | exact resolve eq20 eq179537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179537
  have eq179877 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq179541
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq179541
    | exact resolve eq179541 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179541
  have eq179881 : x = (M.op x y) := by
    first
    | (have r₁ := eq179877
       have r₂ := eq72235
       grind)
    | exact resolve eq179877 eq72235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179877
  have eq180926 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq179881 eq20
    | exact resolve eq20 eq179881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq181040 : x = (M.op x x) := by
    first
    | exact superpose eq179881 eq1412
    | exact resolve eq1412 eq179881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412
  have eq181302 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq180926
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq180926
    | exact resolve eq180926 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180926
  have eq181699 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq181040
       grind)
    | exact superpose eq181040 eq56
    | exact resolve eq56 eq181040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq181915 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq179881 eq181699
    | exact resolve eq181699 eq179881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181699
  have eq181958 : y = (M.op x y) := by
    first
    | (have i₁ := eq181915
       have i₂ := eq181040
       grind)
    | exact superpose eq181040 eq181915
    | exact resolve eq181915 eq181040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181040 eq181915
  have eq181970 : y = (M.op x y) := by
    first
    | (have i₁ := eq181958
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq181958
    | exact resolve eq181958 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq181958
  have eq181975 : x = y := by
    first
    | exact superpose eq179881 eq181970
    | exact resolve eq181970 eq179881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179881 eq181970
  have eq181977 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq181975
       grind)
    | exact superpose eq181975 eq24
    | exact resolve eq24 eq181975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq181975
  have eq182430 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq181977
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq181977
    | exact resolve eq181977 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq181977
  have eq182575 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq181302 eq182430
    | exact resolve eq182430 eq181302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181302 eq182430
  have eq182628 : False := by grind
  exact eq182628
