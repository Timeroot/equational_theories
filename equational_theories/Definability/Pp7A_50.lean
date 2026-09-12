import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyx_pxx_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq24 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq26 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq92 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq24 (τ X0)
       grind)
    | exact superpose eq24 eq19
    | (have j1 := eq24 (τ X0)
       grind)
    | exact resolve eq19 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq24
  have eq96 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq92 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92
    | (have j0 := eq92 X0
       grind)
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq100 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq96 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq96
    | (have j0 := eq96 X0
       grind)
    | exact resolve eq96 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq104 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq100 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq100 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq100 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq128 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq26
    | (have j0 := eq26 X0 X1
       have j1 := eq14 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq26 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq104 (σ X0)
       grind)
    | exact superpose eq104 eq15
    | exact resolve eq15 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq174
    | exact resolve eq174 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq174
  have eq1398 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1444 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1398 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1398
    | (have j0 := eq1398 X0 X1
       grind)
    | exact resolve eq1398 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398
  have eq5022 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq128 x y
       grind)
    | exact superpose eq128 eq16
    | (have j1 := eq128 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq128 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq128 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq128 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq5048 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq5022
  have eq5447 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5048
       grind)
    | exact superpose eq5048 eq16
    | exact resolve eq16 eq5048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5449 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq5048
       grind)
    | exact superpose eq5048 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq5048
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq5048
       grind)
    | exact resolve eq12 eq5048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5048
  have eq5465 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq5449
  have eq5476 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5465
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq5465
    | exact resolve eq5465 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5465
  have eq9849 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1444 y x
       have i₂ := eq5476
       grind)
    | exact superpose eq5476 eq1444
    | (have j0 := eq1444 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq1444 eq5476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444 eq5476
  have eq9876 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq9849
  have eq9892 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq9876
       have r₂ := eq5447
       grind)
    | exact resolve eq9876 eq5447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5447 eq9876
  have eq13419 : x ≠ x ∨ x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq9892
       grind)
    | exact superpose eq9892 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq9892
       grind)
    | exact resolve eq12 eq9892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13435 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq13419
  have eq18192 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26 x y
       have i₂ := eq13435
       grind)
    | exact superpose eq13435 eq26
    | (have j0 := eq26 x y
       grind)
    | exact resolve eq26 eq13435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq13435
  have eq18195 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18192
  have eq23770 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq18195
       grind)
    | exact superpose eq18195 eq16
    | exact resolve eq16 eq18195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18195
  have eq29556 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23770
       have i₂ := eq9892
       grind)
    | exact superpose eq9892 eq23770
    | exact resolve eq23770 eq9892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9892 eq23770
  have eq29557 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq29556
  have eq29558 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq29557
  have eq38089 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq29558
       grind)
    | exact superpose eq29558 eq10
    | exact resolve eq10 eq29558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29558
  have eq38209 : x = y ∨ x = y := by
    first
    | (have i₁ := eq38089
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq38089
    | exact resolve eq38089 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38089
  have eq38210 : x = y := by grind
  clear eq38209
  have eq46551 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38210
       grind)
    | exact superpose eq38210 eq16
    | exact resolve eq16 eq38210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38210
  have eq46552 : False := by grind
  exact eq46552

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_x_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op y (M.op x y)) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have i₂ := eq14 (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : x ≠ (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) := by
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
  have eq76 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq112
    | exact resolve eq112 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq113
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq113
    | exact resolve eq113 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq133 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq156 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq133 eq16
    | exact resolve eq16 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq213 : (M.op (M.op (M.op y (M.op x y)) x) (M.op (M.op y (M.op x y)) x)) = (k (M.op (M.op y (M.op x y)) x) (M.op (M.op y (M.op x y)) x)) := by grind
  have eq214 : (M.op (M.op y (M.op x y)) x) = (k (M.op (M.op y (M.op x y)) x) (M.op (M.op y (M.op x y)) x)) := by
    first
    | exact superpose eq51 eq213
    | exact resolve eq213 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq213
  have eq219 : (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) = (k (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) := by grind
  have eq220 : (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) = (k (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) := by
    first
    | exact superpose eq52 eq219
    | exact resolve eq219 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq219
  have eq632 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq54 (M.op X0 X0) x x X3
       have i₂ := eq53 X0 x x (M.op X0 X0)
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq54
  have eq816 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq94 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq8231 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8232 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8231
    | exact resolve eq8231 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8231
  have eq8243 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq8232
       have r₂ := eq28
       grind)
    | exact resolve eq8232 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8232
  have eq8245 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8243
    | exact resolve eq8243 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8243
  have eq8252 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq8245
  have eq8264 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq8252
    | exact resolve eq8252 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8252
  have eq8325 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq8264 eq114
    | exact resolve eq114 eq8264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8264
  have eq8334 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8325
  have eq8336 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8334
       have r₂ := eq28
       grind)
    | exact resolve eq8334 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8334
  have eq8343 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8336
  have eq8355 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8343
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq8343
    | exact resolve eq8343 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8343
  have eq8717 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq8355
       grind)
    | exact superpose eq8355 eq72
    | exact resolve eq72 eq8355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8355
  have eq8733 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq8717
    | exact resolve eq8717 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8717
  have eq8804 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8733 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq8733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8807 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq8804
    | exact resolve eq8804 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8804
  have eq8818 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8807
       have r₂ := eq28
       grind)
    | exact resolve eq8807 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8807
  have eq8820 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq8818
    | exact resolve eq8818 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8818
  have eq8821 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8820
  have eq8888 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8821
  have eq8902 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq8888
    | exact resolve eq8888 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8888
  have eq9509 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8902 eq8733
    | exact resolve eq8733 eq8902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8733 eq8902
  have eq9513 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9509
  have eq9517 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9513
       have r₂ := eq28
       grind)
    | exact resolve eq9513 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9513
  have eq9521 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9517 eq76
    | (have r₁ := eq76
       have r₂ := eq9517
       grind)
    | exact resolve eq76 eq9517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq9517
  have eq9525 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq9521
  have eq10943 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9525 eq83
    | exact resolve eq83 eq9525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq9525
  have eq10975 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq10943
    | exact resolve eq10943 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq10943
  have eq10985 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq10975
  have eq11001 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq10985
    | exact resolve eq10985 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10985
  have eq11088 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11001 eq114
    | exact resolve eq114 eq11001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq11103 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) := by grind
  clear eq11088
  have eq11107 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | (have r₁ := eq11103
       have r₂ := eq75
       grind)
    | exact resolve eq11103 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq11103
  have eq11109 : y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq11107
       have r₂ := eq28
       grind)
    | exact resolve eq11107 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11107
  have eq12112 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11109
       grind)
    | exact superpose eq11109 eq72
    | exact resolve eq72 eq11109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12123 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq11109
       grind)
    | exact superpose eq11109 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq11109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11109
  have eq12124 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq12123
  have eq12126 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12124
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12124
    | exact resolve eq12124 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12124
  have eq12136 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12112
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12112
    | exact resolve eq12112 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12112
  have eq12138 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12126
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12126
    | exact resolve eq12126 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12126
  have eq12207 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq12138
  have eq12223 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12207
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12207
    | exact resolve eq12207 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12207
  have eq12537 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq12223
       grind)
    | exact superpose eq12223 eq72
    | exact resolve eq72 eq12223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12565 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq12537
    | exact resolve eq12537 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12537
  have eq13403 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12565 eq11001
    | exact resolve eq11001 eq12565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11001 eq12565
  have eq13410 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq13403
  have eq13419 : y = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq13410
       have r₂ := eq28
       grind)
    | exact resolve eq13410 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13410
  have eq15395 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12223
       have i₂ := eq13419
       grind)
    | exact superpose eq13419 eq12223
    | exact resolve eq12223 eq13419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12223 eq13419
  have eq15403 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq15395
  have eq15551 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15403 eq21
    | exact resolve eq21 eq15403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15599 : (M.op (M.op y y) x) = (k (M.op (M.op y y) x) (M.op (M.op y y) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15403 eq214
    | exact resolve eq214 eq15403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq15403
  have eq15617 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15599
       have i₂ := eq632 y x
       grind)
    | (have i₁ := eq15599
       have i₂ := eq632 x (M.op (M.op y y) x)
       grind)
    | exact superpose eq632 eq15599
    | exact resolve eq15599 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15599
  have eq15664 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15551
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15551
    | exact resolve eq15551 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15551
  have eq15779 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15664 eq27
    | exact resolve eq27 eq15664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15664
  have eq15944 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq816 x x
       have i₂ := eq15617
       grind)
    | exact superpose eq15617 eq816
    | (have j0 := eq816 x x
       grind)
    | exact resolve eq816 eq15617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15617
  have eq15947 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq15944
  have eq15948 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq15947
  have eq15957 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15948
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15948
    | exact resolve eq15948 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15948
  have eq16443 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15957 eq632
    | exact resolve eq632 eq15957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15957
  have eq16593 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16443 eq15779
    | exact resolve eq15779 eq16443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15779 eq16443
  have eq16645 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16593
  have eq16679 : x = (M.op x y) := by
    first
    | (have r₁ := eq16645
       have r₂ := eq28
       grind)
    | exact resolve eq16645 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16645
  have eq16684 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq16679 eq21
    | exact resolve eq21 eq16679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq16793 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq16684
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16684
    | exact resolve eq16684 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16684
  have eq16794 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq16793 eq27
    | exact resolve eq27 eq16793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16871 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16793 eq12136
    | exact resolve eq12136 eq16793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12136
  have eq17156 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16871 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq16871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17157 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16794 eq17156
    | exact resolve eq17156 eq16794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17156
  have eq17171 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16794 eq17157
    | exact resolve eq17157 eq16794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17157
  have eq17183 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq17171
       have r₂ := eq28
       grind)
    | exact resolve eq17171 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17171
  have eq19640 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq17183
  have eq19660 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16794 eq19640
    | exact resolve eq19640 eq16794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19640
  have eq20442 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq19660 eq16871
    | exact resolve eq16871 eq19660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16871 eq19660
  have eq20450 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20442
  have eq20471 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20450
  have eq20491 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20471
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20471
    | exact resolve eq20471 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20471
  have eq20503 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16679 eq20491
    | exact resolve eq20491 eq16679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20491
  have eq20667 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq20503
       grind)
    | exact superpose eq20503 eq72
    | exact resolve eq72 eq20503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq20685 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq816 x y
       have i₂ := eq20503
       grind)
    | exact superpose eq20503 eq816
    | (have j0 := eq816 x y
       grind)
    | exact resolve eq816 eq20503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816 eq20503
  have eq20690 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20685
  have eq20699 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20690
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20690
    | exact resolve eq20690 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20690
  have eq20711 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16793 eq20667
    | exact resolve eq20667 eq16793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20667
  have eq20713 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20699
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20699
    | exact resolve eq20699 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20699
  have eq20725 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20711
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20711
    | exact resolve eq20711 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20711
  have eq20727 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq20713
    | exact resolve eq20713 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq20713
  have eq20736 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16793 eq20725
    | exact resolve eq20725 eq16793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20725
  have eq20738 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16793 eq20727
    | exact resolve eq20727 eq16793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20727
  have eq20743 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq20738
       have r₂ := eq28
       grind)
    | exact resolve eq20738 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20738
  have eq20748 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20743
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20743
    | exact resolve eq20743 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20743
  have eq20752 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16793 eq20748
    | exact resolve eq20748 eq16793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20748
  have eq20756 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20752
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20752
    | exact resolve eq20752 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20752
  have eq21574 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20756
  have eq21594 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16794 eq21574
    | exact resolve eq21574 eq16794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16794 eq21574
  have eq22385 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21594 eq20736
    | exact resolve eq20736 eq21594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20736 eq21594
  have eq22392 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22385
  have eq22396 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq22392
       have r₂ := eq28
       grind)
    | exact resolve eq22392 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22392
  have eq22410 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq22396 eq28
    | exact resolve eq28 eq22396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq22414 : (M.op (M.op (σ y) (σ y)) (σ x)) = (k (M.op (M.op (σ y) (σ y)) (σ x)) (M.op (M.op (σ y) (σ y)) (σ x))) := by
    first
    | exact superpose eq22396 eq220
    | exact resolve eq220 eq22396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq22396
  have eq22424 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq22414
       have i₂ := eq632 sF3 sF2
       grind)
    | (have i₁ := eq22414
       have i₂ := eq632 x (M.op (M.op sF3 sF3) sF2)
       grind)
    | exact superpose eq632 eq22414
    | exact resolve eq22414 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22414
  have eq22430 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq16793 eq22424
    | exact resolve eq22424 eq16793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22424
  have eq22540 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq22430 eq156
    | exact resolve eq156 eq22430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq22430
  have eq22581 : (τ (σ (M.op x y))) = (k x x) := by
    first
    | exact superpose eq16679 eq22540
    | exact resolve eq22540 eq16679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22540
  have eq22591 : (M.op x y) = (k x x) := by
    first
    | exact superpose eq31 eq22581
    | exact resolve eq22581 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq22581
  have eq22599 : x = (k x x) := by
    first
    | exact superpose eq16679 eq22591
    | exact resolve eq22591 eq16679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22591
  have eq23406 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq22599
       grind)
    | exact superpose eq22599 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq22599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22599
  have eq23407 : x = (M.op x x) := by grind
  clear eq23406
  have eq23486 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq632 x X0
       have i₂ := eq23407
       grind)
    | exact superpose eq23407 eq632
    | exact resolve eq632 eq23407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632 eq23407
  have eq23942 : y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq23486 y
       grind)
    | exact superpose eq23486 eq19
    | (have j1 := eq23486 y
       grind)
    | exact resolve eq19 eq23486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq23486
  have eq24033 : x = y := by
    first
    | exact superpose eq16679 eq23942
    | exact resolve eq23942 eq16679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16679 eq23942
  have eq24043 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq24033
       grind)
    | exact superpose eq24033 eq25
    | exact resolve eq25 eq24033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq24033
  have eq24193 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24043
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24043
    | exact resolve eq24043 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq24043
  have eq24256 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq16793 eq24193
    | exact resolve eq24193 eq16793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16793 eq24193
  have eq24302 : False := by grind
  exact eq24302

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxx_pyx_pxy_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq52 : ∀ X0 : G, (M.op (M.op (M.op y (M.op x y)) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 X0 y x
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq30 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30
    | (have j0 := eq30 x
       grind)
    | exact resolve eq30 eq22
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
  clear eq31
  have eq76 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op y (M.op x y)) x)) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op y (M.op x y)) x)) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq91 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq130 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq215 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X1) ≠ (M.op (M.op X0 (M.op X1 X0)) X1) ∨ (M.op X2 X2) = X2 ∨ (k (M.op (M.op X0 (M.op X1 X0)) X1) X2) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 (M.op X1 X0)) X1) X2
       have i₂ := eq9 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op (M.op X0 (M.op X1 X0)) X1) X2
       grind)
    | (have r₁ := eq13 (M.op (M.op X1 (M.op X2 X1)) X2) X1
       have r₂ := eq9 (M.op (M.op X1 (M.op X2 X1)) X2) X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 (M.op X1 X0)) X1) X2) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) X1)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq215 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq266 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq76 eq77
    | exact resolve eq77 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq77
  have eq309 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) X0
       have i₂ := eq266 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq266 eq9
    | exact resolve eq9 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq312 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq266 X0 (M.op X0 X0)
       grind)
    | exact superpose eq266 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq266 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq312 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq326 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ X0) (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq130 X0 (M.op X1 X1)
       have i₂ := eq313 X1 X0
       grind)
    | exact superpose eq313 eq130
    | exact resolve eq130 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq380 : ∀ X0 : G, (τ (M.op (σ x) (σ x))) = (k x (τ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq38 eq326
    | exact resolve eq326 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : ∀ X0 : G, (τ (M.op (σ y) (σ y))) = (k y (τ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq39 eq326
    | exact resolve eq326 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq675 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq57
       have i₂ := eq14 sF2 sF2
       grind)
    | exact superpose eq14 eq57
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq679 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq63
       have i₂ := eq14 sF2 sF3
       grind)
    | exact superpose eq14 eq63
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq63 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq682 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq675
  have eq687 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq679
    | exact resolve eq679 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq1090 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq682
       grind)
    | exact superpose eq682 eq10
    | exact resolve eq10 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1187 : ∀ X0 : G, (k x x) = (k x (τ (M.op X0 X0))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq1090 eq380
    | exact resolve eq380 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1407 : ∀ X0 X1 X2 : G, (k (σ (M.op (M.op X1 (M.op X2 X1)) X2)) X0) = (σ (M.op (τ X0) (M.op (M.op X1 (M.op X2 X1)) X2))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq220 X1 X2 (τ X0)
       grind)
    | exact superpose eq220 eq48
    | (have j1 := eq220 X0 X1 (τ X0)
       grind)
    | exact resolve eq48 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq220
  have eq47590 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq687
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq687
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq687 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq47620 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq47590
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq47590
    | exact resolve eq47590 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47590
  have eq47623 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq47620
    | exact resolve eq47620 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47620
  have eq47624 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq47623
       have r₂ := eq27
       grind)
    | exact resolve eq47623 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47623
  have eq48255 : ∀ X0 X1 : G, (σ (M.op x (M.op (M.op X0 (M.op X1 X0)) X1))) = (k (σ (M.op (M.op X0 (M.op X1 X0)) X1)) (σ x)) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq38 eq1407
    | exact resolve eq1407 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407
  have eq48570 : ∀ X0 X1 : G, (σ (k (M.op (M.op X0 (M.op X1 X0)) X1) x)) = (σ (M.op x (M.op (M.op X0 (M.op X1 X0)) X1))) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq30 eq48255
    | exact resolve eq48255 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq48255
  have eq48864 : (τ (σ y)) = (k y (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq47624 eq381
    | exact resolve eq381 eq47624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381 eq47624
  have eq49115 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq39 eq48864
    | exact resolve eq48864 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq48864
  have eq49531 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq49115
       grind)
    | exact superpose eq49115 eq14
    | (have j0 := eq14 y y
       grind)
    | exact resolve eq14 eq49115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49115
  have eq49533 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq49531
  have eq49570 : (τ (σ x)) = (k x (τ (σ x))) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq49533 eq380
    | exact resolve eq380 eq49533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq49533
  have eq49803 : x = (k x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq38 eq49570
    | exact resolve eq49570 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49570
  have eq50553 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq49803
       grind)
    | exact superpose eq49803 eq14
    | (have j0 := eq14 x x
       grind)
    | exact resolve eq14 eq49803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49803
  have eq50555 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq50553
  have eq50560 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq266 y X0
       have i₂ := eq50555
       grind)
    | exact superpose eq50555 eq266
    | exact resolve eq266 eq50555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50562 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 y) X0) X1) = X1 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq309 X0 y X1
       have i₂ := eq50555
       grind)
    | exact superpose eq50555 eq309
    | exact resolve eq309 eq50555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50563 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq313 y X0
       have i₂ := eq50555
       grind)
    | exact superpose eq50555 eq313
    | exact resolve eq313 eq50555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50565 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) (τ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq326 X0 y
       have i₂ := eq50555
       grind)
    | exact superpose eq50555 eq326
    | exact resolve eq326 eq50555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50555
  have eq51260 : ∀ X0 X1 : G, (M.op (M.op y (M.op X0 X0)) X1) = X1 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq50562 (M.op y (M.op X0 X0)) X1
       have i₂ := eq309 y X0 (M.op y (M.op X0 X0))
       grind)
    | exact superpose eq309 eq50562
    | exact resolve eq50562 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq50562
  have eq55509 : (τ y) = (k (τ y) (τ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq50565 y
       have i₂ := eq50560 y
       grind)
    | exact superpose eq50560 eq50565
    | exact resolve eq50565 eq50560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50560 eq50565
  have eq55814 : (τ y) = (k (τ y) (τ y)) ∨ x = (M.op x x) := by grind
  clear eq55509
  have eq56001 : (σ (τ y)) = (k y (σ (τ y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq49 y (τ y)
       have i₂ := eq55814
       grind)
    | exact superpose eq55814 eq49
    | exact resolve eq49 eq55814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq55814
  have eq56016 : y = (k y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq56001
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq56001
    | exact resolve eq56001 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56001
  have eq56046 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq659 y y
       have i₂ := eq56016
       grind)
    | exact superpose eq56016 eq659
    | (have j0 := eq659 y y
       grind)
    | exact resolve eq659 eq56016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659 eq56016
  have eq56050 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq56046
  have eq56057 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq56050
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq56050
    | exact resolve eq56050 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56050
  have eq56087 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq56057 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) x
       have r₂ := eq56057
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq56057
       grind)
    | exact resolve eq13 eq56057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56091 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq56057 eq313
    | exact resolve eq313 eq56057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56057
  have eq56237 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq56087 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56087
  have eq59025 : (σ (k (M.op x y) y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq56091 eq34
    | exact resolve eq34 eq56091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq56091
  have eq64400 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq59025
       have i₂ := eq50563 sF0
       grind)
    | exact superpose eq50563 eq59025
    | exact resolve eq59025 eq50563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50563 eq59025
  have eq64426 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x x) := by grind
  clear eq64400
  have eq67652 : (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq64426 eq10
    | exact resolve eq10 eq64426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64426
  have eq68646 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq67652 eq326
    | exact resolve eq326 eq67652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq68678 : (k x x) = (k x (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq67652 eq1187
    | exact resolve eq1187 eq67652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187 eq67652
  have eq68876 : (k x x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq68678
       have i₂ := eq313 sF0 x
       grind)
    | exact superpose eq313 eq68678
    | exact resolve eq68678 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68678
  have eq68903 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq68646 X0
       have i₂ := eq313 sF0 (τ X0)
       grind)
    | exact superpose eq313 eq68646
    | exact resolve eq68646 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq68646
  have eq68977 : (k x x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq12 x x
       grind)
    | (have r₁ := eq68876
       have r₂ := eq12 x (σ x)
       grind)
    | (have r₁ := eq68876
       have r₂ := eq12 x x
       grind)
    | exact resolve eq68876 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68876
  have eq69010 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq682
       have i₂ := eq68977
       grind)
    | exact superpose eq68977 eq682
    | exact resolve eq682 eq68977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682 eq68977
  have eq69040 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq69010
  have eq511223 : (σ (M.op x y)) = (σ (k y x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq48570 y y
       have i₂ := eq51260 y y
       grind)
    | exact superpose eq51260 eq48570
    | exact resolve eq48570 eq51260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48570 eq51260
  have eq511226 : (σ (M.op x y)) = (σ (k y x)) ∨ x = (M.op x x) := by grind
  clear eq511223
  have eq511229 : (σ (M.op x y)) = (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq511226
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq511226
    | exact resolve eq511226 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511226
  have eq511231 : (σ (M.op x y)) = (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq511229
    | exact resolve eq511229 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511229
  have eq813452 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq56237 eq58
    | (have j1 := eq56237 (σ x)
       grind)
    | exact resolve eq58 eq56237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq56237
  have eq813454 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq813452
    | exact resolve eq813452 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813452
  have eq813458 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq511231
       have i₂ := eq813454
       grind)
    | exact superpose eq813454 eq511231
    | exact resolve eq511231 eq813454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511231 eq813454
  have eq813460 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq813458
  have eq813463 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq813460
       have r₂ := eq27
       grind)
    | exact resolve eq813460 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813460
  have eq813680 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq813463 eq68903
    | exact resolve eq68903 eq813463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68903 eq813463
  have eq813923 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by grind
  clear eq813680
  have eq814033 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq38 eq813923
    | exact resolve eq813923 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq813923
  have eq814034 : x = (M.op x x) := by grind
  clear eq814033
  have eq814269 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq69040
       have i₂ := eq814034
       grind)
    | exact superpose eq814034 eq69040
    | exact resolve eq69040 eq814034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69040
  have eq814369 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq814269
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq814269
    | exact resolve eq814269 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq814269
  have eq814370 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq814369
  have eq845958 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq266 x X0
       have i₂ := eq814034
       grind)
    | exact superpose eq814034 eq266
    | exact resolve eq266 eq814034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814034
  have eq846029 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq845958 y
       grind)
    | exact superpose eq845958 eq18
    | (have j1 := eq845958 y
       grind)
    | exact resolve eq18 eq845958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq845958
  have eq846063 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq846029 eq20
    | exact resolve eq20 eq846029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq846029
  have eq852998 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq846063
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq846063
    | exact resolve eq846063 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq846063
  have eq854081 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq852998 eq26
    | exact resolve eq26 eq852998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq852998
  have eq863966 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq814370 eq266
    | exact resolve eq266 eq814370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq814370
  have eq864027 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq863966 eq854081
    | exact resolve eq854081 eq863966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854081 eq863966
  have eq864031 : False := by grind
  exact eq864031

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxx_pxy_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq174 : ∀ X0 : G, (M.op (M.op (M.op y (M.op x y)) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op y (M.op x y)) x)) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op y (M.op x y)) x)) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq644 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq180 eq181
    | exact resolve eq181 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq181
  have eq1163 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
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
  have eq1164 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1247 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1259 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1247 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq1247 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq1247 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1247
  have eq1294 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq644 X0 X1
       have i₂ := eq1259 X0
       grind)
    | exact superpose eq1259 eq644
    | exact resolve eq644 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq1342 : ∀ X0 X1 : G, (M.op (σ (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1294 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1294
    | exact resolve eq1294 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9802 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1163
       grind)
    | exact superpose eq1163 eq39
    | exact resolve eq39 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq9803 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9802
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9802
    | exact resolve eq9802 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9802
  have eq9805 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq9803
    | exact resolve eq9803 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9803
  have eq9807 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq9805
       have i₂ := eq1259 x
       grind)
    | exact superpose eq1259 eq9805
    | exact resolve eq9805 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9805
  have eq314849 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq9807 eq1164
    | exact resolve eq1164 eq9807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq314858 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq314849
       have r₂ := eq27
       grind)
    | exact resolve eq314849 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314849
  have eq314865 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq314858
       have i₂ := eq1259 sF2
       grind)
    | exact superpose eq1259 eq314858
    | exact resolve eq314858 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314858
  have eq314869 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq314865 eq12
    | (have j0 := eq12 x (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq314865
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq314865
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq314865
       grind)
    | exact resolve eq12 eq314865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314865
  have eq314897 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq314869
       have r₂ := eq26
       grind)
    | exact resolve eq314869 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314869
  have eq314904 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq314897
       have i₂ := eq1259 sF2
       grind)
    | exact superpose eq1259 eq314897
    | exact resolve eq314897 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314897
  have eq314905 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq314904
  have eq314910 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq9807 eq314905
    | exact resolve eq314905 eq9807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9807 eq314905
  have eq314911 : (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq314910
       have r₂ := eq27
       grind)
    | exact resolve eq314910 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314910
  have eq314916 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq314911 eq141
    | exact resolve eq141 eq314911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314911
  have eq315279 : x = (k x x) ∨ x = (k x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq29 eq314916
    | exact resolve eq314916 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314916
  have eq315280 : (M.op x y) = (M.op y x) ∨ x = (k x x) := by grind
  clear eq315279
  have eq315322 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x x) ∨ (M.op x y) = (k y x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq315280
       grind)
    | exact superpose eq315280 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq315280
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq315280
       grind)
    | exact resolve eq12 eq315280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315280
  have eq315350 : x = (M.op x x) ∨ (M.op x y) = (k y x) ∨ x = (k x x) := by
    first
    | (have r₁ := eq315322
       have r₂ := eq18
       grind)
    | exact resolve eq315322 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315322
  have eq315357 : x = (k x x) ∨ (M.op x y) = (k y x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq315350
       have i₂ := eq1259 x
       grind)
    | exact superpose eq1259 eq315350
    | exact resolve eq315350 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315350
  have eq315358 : (M.op x y) = (k y x) ∨ x = (k x x) := by grind
  clear eq315357
  have eq315366 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq315358
       grind)
    | exact superpose eq315358 eq39
    | exact resolve eq39 eq315358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq315358
  have eq315368 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq315366
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq315366
    | exact resolve eq315366 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315366
  have eq315372 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq20 eq315368
    | exact resolve eq315368 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315368
  have eq315377 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq315372 eq1164
    | exact resolve eq1164 eq315372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164
  have eq315386 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have r₁ := eq315377
       have r₂ := eq27
       grind)
    | exact resolve eq315377 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315377
  have eq315393 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq315386
       have i₂ := eq1259 sF2
       grind)
    | exact superpose eq1259 eq315386
    | exact resolve eq315386 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315386
  have eq417970 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq315393 eq12
    | (have j0 := eq12 x (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq315393
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq315393
       grind)
    | exact resolve eq12 eq315393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315393
  have eq418009 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have r₁ := eq417970
       have r₂ := eq26
       grind)
    | exact resolve eq417970 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417970
  have eq418018 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq418009
       have i₂ := eq1259 sF2
       grind)
    | exact superpose eq1259 eq418009
    | exact resolve eq418009 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259 eq418009
  have eq418019 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (k x x) := by grind
  clear eq418018
  have eq418025 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq315372 eq418019
    | exact resolve eq418019 eq315372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315372 eq418019
  have eq418026 : (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have r₁ := eq418025
       have r₂ := eq27
       grind)
    | exact resolve eq418025 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418025
  have eq418032 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k x x) := by
    first
    | exact superpose eq418026 eq141
    | exact resolve eq141 eq418026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq418026
  have eq418422 : x = (k x x) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq418032
    | exact resolve eq418032 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq418032
  have eq418423 : x = (k x x) := by grind
  clear eq418422
  have eq418479 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1294 x X0
       have i₂ := eq418423
       grind)
    | exact superpose eq418423 eq1294
    | exact resolve eq1294 eq418423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294
  have eq418493 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1342 x X0
       have i₂ := eq418423
       grind)
    | exact superpose eq418423 eq1342
    | exact resolve eq1342 eq418423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342 eq418423
  have eq418845 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq418493 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq418493
    | (have j0 := eq418493 X0
       grind)
    | exact resolve eq418493 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq418493
  have eq418906 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq418479 y
       grind)
    | exact superpose eq418479 eq18
    | (have j1 := eq418479 y
       grind)
    | exact resolve eq18 eq418479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq418479
  have eq423096 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq418906
       grind)
    | exact superpose eq418906 eq24
    | exact resolve eq24 eq418906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq418906
  have eq423396 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq423096 eq20
    | exact resolve eq20 eq423096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq423096
  have eq424213 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq418845 eq26
    | (have j1 := eq418845 (σ y)
       grind)
    | exact resolve eq26 eq418845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq418845
  have eq424617 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq424213 eq27
    | exact resolve eq27 eq424213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq424213
  have eq424780 : False := by grind
  exact eq424780

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pxx_y_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq174 : ∀ X0 : G, (M.op (M.op (M.op y (M.op x y)) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op y (M.op x y)) x)) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op y (M.op x y)) x)) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (M.op (M.op y (M.op x y)) x) ≠ (M.op (M.op y (M.op x y)) x) ∨ (M.op X0 X0) = (k X0 (M.op (M.op y (M.op x y)) x)) := by
    intro X0
    first
    | exact superpose eq174 eq13
    | (have j0 := eq13 X0 (M.op (M.op y (M.op x y)) x)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op y (M.op x y)) x)
       have r₂ := eq174 (M.op (M.op y (M.op x y)) x)
       grind)
    | exact resolve eq13 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op y (M.op x y)) x)) := by
    intro X0
    first
    | (have j0 := eq182 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq644 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq180 eq181
    | exact resolve eq181 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq181
  have eq694 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq644 X0 (M.op X0 X0)
       grind)
    | exact superpose eq644 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq644 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq694 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq733 : ∀ X0 X1 X2 : G, (M.op (k X0 (M.op X1 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq644 X0 X2
       have i₂ := eq695 X1 X0
       grind)
    | exact superpose eq695 eq644
    | exact resolve eq644 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : ∀ X0 : G, (σ (M.op x x)) = (k (σ x) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq35 (M.op X0 X0)
       have i₂ := eq695 X0 x
       grind)
    | exact superpose eq695 eq35
    | exact resolve eq35 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq746 : ∀ X0 : G, (τ (M.op (σ x) (σ x))) = (k x (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq90 (M.op X0 X0)
       have i₂ := eq695 X0 sF2
       grind)
    | exact superpose eq695 eq90
    | exact resolve eq90 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq695
  have eq1184 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq1185 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1242 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1243 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1242 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242
  have eq1529 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1184
       grind)
    | exact superpose eq1184 eq39
    | exact resolve eq39 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1184
  have eq1530 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1529
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1529
    | exact resolve eq1529 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529
  have eq1532 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1530
    | exact resolve eq1530 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1530
  have eq1756 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1532 eq1185
    | exact resolve eq1185 eq1532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185 eq1532
  have eq1763 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1756
       have r₂ := eq27
       grind)
    | exact resolve eq1756 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1756
  have eq1786 : (τ (σ x)) = (k x (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1763 eq746
    | exact resolve eq746 eq1763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1763
  have eq1792 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq1786
    | exact resolve eq1786 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786
  have eq1799 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq1243 x
       grind)
    | (have r₁ := eq1792
       have r₂ := eq1243 x
       grind)
    | exact resolve eq1792 eq1243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792
  have eq1808 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq644 x X0
       have i₂ := eq1799
       grind)
    | exact superpose eq1799 eq644
    | exact resolve eq644 eq1799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1799
  have eq1839 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1808 y
       grind)
    | exact superpose eq1808 eq18
    | (have j1 := eq1808 y
       grind)
    | exact resolve eq18 eq1808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1808
  have eq1869 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1839
  have eq1884 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ y)) (σ x)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1869 eq175
    | exact resolve eq175 eq1869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq1869
  have eq1895 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1884 X0
       have i₂ := eq644 sF3 sF2
       grind)
    | exact superpose eq644 eq1884
    | exact resolve eq1884 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1884
  have eq1924 : (τ (σ x)) = (k x (τ (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1895 eq746
    | exact resolve eq746 eq1895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746 eq1895
  have eq1930 : x = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq1924
    | exact resolve eq1924 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1924
  have eq1955 : x ≠ x ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1243 x
       have i₂ := eq1930
       grind)
    | exact superpose eq1930 eq1243
    | (have j0 := eq1243 x
       grind)
    | (have r₁ := eq1243 x
       have r₂ := eq1930
       grind)
    | exact resolve eq1243 eq1930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1930
  have eq1956 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq1955
  have eq1967 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq644 x X0
       have i₂ := eq1956
       grind)
    | exact superpose eq1956 eq644
    | exact resolve eq644 eq1956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1956
  have eq2032 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1967 y
       grind)
    | exact superpose eq1967 eq18
    | (have j1 := eq1967 y
       grind)
    | exact resolve eq18 eq1967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1967
  have eq2062 : y = (M.op x y) := by grind
  clear eq2032
  have eq2088 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2062
       grind)
    | exact superpose eq2062 eq24
    | exact resolve eq24 eq2062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2091 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) (M.op x y)) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq2062
       grind)
    | exact superpose eq2062 eq174
    | exact resolve eq174 eq2062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq2094 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op (M.op x y) (M.op x y)) x)) := by
    intro X0
    first
    | (have i₁ := eq183 X0
       have i₂ := eq2062
       grind)
    | exact superpose eq2062 eq183
    | exact resolve eq183 eq2062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq2062
  have eq2099 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq2094 X0
       have i₂ := eq644 sF0 x
       grind)
    | exact superpose eq644 eq2094
    | exact resolve eq2094 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2094
  have eq2102 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2091 X0
       have i₂ := eq644 sF0 x
       grind)
    | exact superpose eq644 eq2091
    | exact resolve eq2091 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644 eq2091
  have eq2110 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2088 eq20
    | exact resolve eq20 eq2088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2088
  have eq2686 : ∀ X0 X1 : G, (M.op (k X0 x) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq733 X0 x X1
       have i₂ := eq2102 x
       grind)
    | exact superpose eq2102 eq733
    | exact resolve eq733 eq2102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq2689 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq742 x
       have i₂ := eq2102 x
       grind)
    | exact superpose eq2102 eq742
    | exact resolve eq742 eq2102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq2102
  have eq2703 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2689
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2689
    | exact resolve eq2689 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2689
  have eq2729 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2703 eq1243
    | (have j0 := eq1243 (σ x)
       grind)
    | (have r₁ := eq1243 (σ x)
       have r₂ := eq2703
       grind)
    | exact resolve eq1243 eq2703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243 eq2703
  have eq2730 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2729
  have eq2732 : (σ x) = (k (σ x) x) := by
    first
    | (have i₁ := eq2730
       have i₂ := eq2099 sF2
       grind)
    | exact superpose eq2099 eq2730
    | exact resolve eq2730 eq2099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2099 eq2730
  have eq2931 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq2732 eq2686
    | exact resolve eq2686 eq2732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2686 eq2732
  have eq3051 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2931 eq26
    | (have j1 := eq2931 (σ y)
       grind)
    | exact resolve eq26 eq2931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2931
  have eq3125 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq3051 eq27
    | exact resolve eq27 eq3051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3051
  have eq3138 : False := by grind
  exact eq3138

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pxy_pyy_pyx_Equation3008 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq14 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq69 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq81 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq81
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq81
    | exact resolve eq81 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq88 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq87
    | exact resolve eq87 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq88
    | exact resolve eq88 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq103 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq52 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq52 X1 (M.op X0 X0) X0
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq451 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq103 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq103
    | (have j0 := eq103 (σ X0)
       grind)
    | exact resolve eq103 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq551 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 x X0 X1 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 x X0 X1 y
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq51
    | (have j0 := eq51 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq51 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X1 x (M.op X0 X0) X2
       have i₂ := eq52 x (M.op X0 X0) X0
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1)))) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1)))) := by
    intro X0 X1
    grind
  have eq575 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 (M.op X3 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) X2 X3
       have i₂ := eq51 (M.op (M.op X0 X0) (M.op X1 X1)) X0 X1 (M.op (M.op X0 X0) (M.op X1 X1))
       grind)
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq628 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq362 (M.op X0 X0) x X1
       have i₂ := eq52 x (M.op X0 X0) X0
       grind)
    | exact superpose eq52 eq362
    | exact resolve eq362 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq686 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    grind
  have eq718 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq628 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq628 X0 X1
       grind)
    | exact superpose eq628 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq628 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq628 X1 X1
       grind)
    | exact resolve eq12 eq628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq726 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq718 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq1058 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X1) = (M.op X0 (M.op (M.op X3 X3) (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq560 X3 (M.op X1 X0) (M.op (M.op X2 X2) X1)
       have i₂ := eq560 X2 X1 X0
       grind)
    | exact superpose eq560 eq560
    | exact resolve eq560 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1063 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 X0) x)) := by
    intro X0
    first
    | (have i₁ := eq560 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq560
    | (have j0 := eq560 X0 x y
       grind)
    | exact resolve eq560 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1064 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 X0) (σ x))) := by
    intro X0
    first
    | exact superpose eq27 eq560
    | (have j0 := eq560 X0 (σ x) (σ y)
       grind)
    | exact resolve eq560 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4904 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq451 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq10791 : ∀ X0 : G, (k x x) = (τ (M.op X0 X0)) ∨ (σ x) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq50
       have i₂ := eq726 X0 sF2
       grind)
    | exact superpose eq726 eq50
    | (have j1 := eq726 X0 (σ x)
       grind)
    | exact resolve eq50 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq12066 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq573 X0 X1
       have i₂ := eq367 X0 (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X1 X1)
       grind)
    | exact superpose eq367 eq573
    | exact resolve eq573 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367 eq573
  have eq12067 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12066 X0 X1
       have i₂ := eq575 X0 X1 (M.op X0 X0) X1
       grind)
    | exact superpose eq575 eq12066
    | exact resolve eq12066 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq12066
  have eq12126 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12067 X2 X2
       have i₂ := eq362 X1 X0 (M.op X2 X2)
       grind)
    | (have i₁ := eq12067 X1 X0
       have i₂ := eq362 X0 X1 X2
       grind)
    | exact superpose eq362 eq12067
    | exact resolve eq12067 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq12067
  have eq22162 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq89 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq22163 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq22162
    | exact resolve eq22162 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22162
  have eq22174 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq22163
       have r₂ := eq28
       grind)
    | exact resolve eq22163 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22163
  have eq22176 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq22174
    | exact resolve eq22174 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22174
  have eq22266 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (σ x))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq22176 eq51
    | exact resolve eq51 eq22176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22176
  have eq22271 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq552 eq22266
    | exact resolve eq22266 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq22266
  have eq22346 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22271 eq10791
    | exact resolve eq10791 eq22271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10791 eq22271
  have eq22366 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq22346
  have eq22369 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq22366
    | exact resolve eq22366 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22366
  have eq23242 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) x)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq51 x X0 X1 x
       have i₂ := eq22369
       grind)
    | exact superpose eq22369 eq51
    | exact resolve eq51 eq22369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq22369
  have eq23248 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq551 eq23242
    | exact resolve eq23242 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551 eq23242
  have eq23270 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq103 x
       have i₂ := eq23248
       grind)
    | exact superpose eq23248 eq103
    | (have j0 := eq103 x
       grind)
    | exact resolve eq103 eq23248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23271 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq23270
  have eq23544 : ∀ X0 : G, y = (M.op X0 X0) ∨ x = (M.op X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq23271
       have i₂ := eq628 X0 x
       grind)
    | (have i₁ := eq23271
       have i₂ := eq628 x x
       grind)
    | exact superpose eq628 eq23271
    | exact resolve eq23271 eq628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23271
  have eq24018 : ∀ X0 X1 : G, x = (M.op X0 X0) ∨ (M.op X1 X1) = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq628 X1 X0
       have i₂ := eq23544 X0
       grind)
    | exact superpose eq23544 eq628
    | (have j1 := eq23544 X1
       grind)
    | exact resolve eq628 eq23544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23544
  have eq25291 : ∀ X0 X1 : G, (k x X0) = (M.op x X0) ∨ (M.op X1 X1) = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    grind
  clear eq24018
  have eq31629 : ∀ X0 : G, y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) ∨ y = (M.op X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq23248
       have i₂ := eq25291 x X0
       grind)
    | exact superpose eq25291 eq23248
    | (have j1 := eq25291 X0 x
       grind)
    | exact resolve eq23248 eq25291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23248 eq25291
  have eq31656 : ∀ X0 : G, y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq31629 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31629
  have eq31810 : y ≠ y ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have j0 := eq31656 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31656
  have eq31811 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq31810
  have eq31834 : ∀ X0 : G, y = (M.op X0 X0) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq31811
       have i₂ := eq628 X0 x
       grind)
    | (have i₁ := eq31811
       have i₂ := eq628 x X0
       grind)
    | exact superpose eq628 eq31811
    | exact resolve eq31811 eq628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31845 : (k y x) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  have eq31893 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq686 x x
       have i₂ := eq31811
       grind)
    | exact superpose eq31811 eq686
    | exact resolve eq686 eq31811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31909 : y = (M.op (M.op x y) (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1063 x
       have i₂ := eq31811
       grind)
    | exact superpose eq31811 eq1063
    | exact resolve eq1063 eq31811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063 eq31811
  have eq32337 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq68
       have i₂ := eq31845
       grind)
    | exact superpose eq31845 eq68
    | exact resolve eq68 eq31845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq31845
  have eq32403 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq69
       have i₂ := eq31893 y
       grind)
    | exact superpose eq31893 eq69
    | exact resolve eq69 eq31893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq31893
  have eq33472 : (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq32403
       have i₂ := eq31834 y
       grind)
    | exact superpose eq31834 eq32403
    | exact resolve eq32403 eq31834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32403
  have eq33554 : (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq33472
  have eq33599 : (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq33554
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33554
    | exact resolve eq33554 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33554
  have eq33628 : ∀ X0 : G, (σ y) = (M.op X0 X0) ∨ (σ y) = (M.op X0 X0) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq33599 eq726
    | (have j0 := eq726 X0 (σ y)
       grind)
    | exact resolve eq726 eq33599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq33629 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq33599 eq103
    | (have j0 := eq103 (σ y)
       grind)
    | exact resolve eq103 eq33599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq33599
  have eq33630 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq33629
  have eq33631 : ∀ X0 : G, (σ y) = (M.op X0 X0) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq33628 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33628
  have eq34081 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq33630 eq686
    | exact resolve eq686 eq33630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq34098 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq33630 eq1064
    | exact resolve eq1064 eq33630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064 eq33630
  have eq38560 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op x y)) = (M.op (M.op y x) (M.op (M.op X1 X1) y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq31909 eq1058
    | exact resolve eq1058 eq31909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31909
  have eq39268 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq38560 X0 x
       have i₂ := eq560 x y x
       grind)
    | exact superpose eq560 eq38560
    | exact resolve eq38560 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38560
  have eq86848 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) x) = X0 ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq39268 eq560
    | exact resolve eq560 eq39268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39268
  have eq92416 : (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq86848 sF0
       have i₂ := eq31834 sF0
       grind)
    | exact superpose eq31834 eq86848
    | exact resolve eq86848 eq31834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31834 eq86848
  have eq92465 : (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq92416
  have eq92483 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq32337
       have i₂ := eq92465
       grind)
    | exact superpose eq92465 eq32337
    | exact resolve eq32337 eq92465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32337 eq92465
  have eq92497 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq92483
  have eq92498 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq92497
    | exact resolve eq92497 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92497
  have eq102051 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq34081 eq92498
    | exact resolve eq92498 eq34081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34081 eq92498
  have eq102119 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq102051
  have eq104729 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (σ x)) (M.op (M.op X1 X1) (σ y))) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq34098 eq1058
    | exact resolve eq1058 eq34098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058 eq34098
  have eq104734 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq104729 X0 X0
       have i₂ := eq560 X0 sF3 sF2
       grind)
    | exact superpose eq560 eq104729
    | exact resolve eq104729 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104729
  have eq112258 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) = X0 ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq104734 eq560
    | exact resolve eq560 eq104734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq104734
  have eq126503 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq112258 sF4
       have i₂ := eq33631 sF4
       grind)
    | exact superpose eq33631 eq112258
    | exact resolve eq112258 eq33631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33631 eq112258
  have eq126554 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq126503
  have eq127274 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq126554 eq102119
    | exact resolve eq102119 eq126554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102119 eq126554
  have eq127286 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq127274
  have eq127291 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq127286
       have r₂ := eq28
       grind)
    | exact resolve eq127286 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127286
  have eq127296 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq127291 eq30
    | exact resolve eq30 eq127291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq127291
  have eq127702 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq127296
    | exact resolve eq127296 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq127296
  have eq127703 : x = y := by grind
  clear eq127702
  have eq127704 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq127703
       grind)
    | exact superpose eq127703 eq19
    | exact resolve eq19 eq127703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq127705 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq127703
       grind)
    | exact superpose eq127703 eq25
    | exact resolve eq25 eq127703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq127703
  have eq127960 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq127705
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq127705
    | exact resolve eq127705 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq127705
  have eq128698 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq127960 eq27
    | exact resolve eq27 eq127960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq127960
  have eq128978 : ∀ X0 : G, (M.op x y) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq127704
       have i₂ := eq628 X0 x
       grind)
    | (have i₁ := eq127704
       have i₂ := eq628 x X0
       grind)
    | exact superpose eq628 eq127704
    | exact resolve eq127704 eq628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628 eq127704
  have eq129581 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq128698 eq128978
    | exact resolve eq128978 eq128698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128698
  have eq129850 : ∀ X0 : G, (M.op X0 X0) = (k (M.op x y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12126 x x X0
       have i₂ := eq128978 (M.op x x)
       grind)
    | exact superpose eq128978 eq12126
    | exact resolve eq12126 eq128978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12126
  have eq130013 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq129850 x
       have i₂ := eq128978 x
       grind)
    | exact superpose eq128978 eq129850
    | exact resolve eq129850 eq128978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129850
  have eq130474 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq129581 eq28
    | exact resolve eq28 eq129581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq129581
  have eq130591 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq130013 eq4904
    | (have j0 := eq4904 (M.op x y)
       grind)
    | exact resolve eq4904 eq130013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4904 eq130013
  have eq130598 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq130591
  have eq130604 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq130598
       have i₂ := eq128978 (σ sF0)
       grind)
    | exact superpose eq128978 eq130598
    | exact resolve eq130598 eq128978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128978 eq130598
  have eq130618 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq130604
    | exact resolve eq130604 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq130604
  have eq130621 : False := by grind
  exact eq130621

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_Equation3008 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3008 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq28 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X2 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = (k X2 X0) := by
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
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq44 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq45 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X2 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq28 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq53 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq147 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq424 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq425 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq424 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq430 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq425 X0 X1
       have j1 := eq147 X0 X1
       grind)
    | (have r₁ := eq425 X0 X1
       have r₂ := eq147 X0 X1
       grind)
    | (have r₁ := eq425 X1 X1
       have r₂ := eq147 X1 X1
       grind)
    | exact resolve eq425 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq425
  have eq439 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq430 (σ X0) (σ X1)
       grind)
    | exact superpose eq430 eq15
    | exact resolve eq15 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq444 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq439 X0 X1
       have i₂ := eq430 X0 X1
       grind)
    | exact superpose eq430 eq439
    | exact resolve eq439 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq439
  have eq446 : False := by grind
  exact eq446

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pxy_pxx_pyx_Equation3008 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  have eq174 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq16 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq16 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq383 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq299 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq299
    | exact resolve eq299 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq529 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq175 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq175 eq175
    | exact resolve eq175 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq175 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq175 X1 (M.op X0 X0) X0
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X2 : G, (M.op X2 X2) = (M.op X0 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq175 x (M.op X0 X0) X0
       have i₂ := eq529 (M.op X0 X0) x X2
       grind)
    | (have i₁ := eq175 (M.op X2 X2) (M.op X2 X2) X2
       have i₂ := eq529 X0 x (M.op (M.op X2 X2) (M.op X2 X2))
       grind)
    | exact superpose eq529 eq175
    | exact resolve eq175 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq594 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq560 X0 X1
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq560 X1 X0
       grind)
    | exact superpose eq560 eq13
    | (have j0 := eq13 X2 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq560 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X2 X2)
       have r₂ := eq560 (M.op X2 X2) X2
       grind)
    | exact resolve eq13 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X1 (M.op X2 X2)) X1 X2
       have i₂ := eq560 X0 (M.op X1 (M.op X2 X2))
       grind)
    | (have i₁ := eq16 (M.op X1 (M.op X2 X2)) X1 X2
       have i₂ := eq560 (M.op X1 (M.op X2 X2)) X0
       grind)
    | exact superpose eq560 eq16
    | exact resolve eq16 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq712 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op X1 X1))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X3 (M.op X0 (M.op X1 X1)) x
       have i₂ := eq533 X0 X1 x
       grind)
    | exact superpose eq533 eq16
    | exact resolve eq16 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq797 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq712 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq712
    | (have j0 := eq712 x X0 y
       grind)
    | exact resolve eq712 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq798 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq26 eq712
    | (have j0 := eq712 (σ x) X0 (σ y)
       grind)
    | exact resolve eq712 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq1513 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq594 X0 (M.op X1 X1) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq1529 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
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
  have eq1532 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1662 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 x x
       have i₂ := eq560 X0 x
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq560 X0 x
       grind)
    | exact superpose eq560 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq560 X0 X0
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq560 x x
       grind)
    | exact resolve eq12 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1680 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1683 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1662 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1662
  have eq1685 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1680 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq1680 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq1680 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1680
  have eq1860 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175 X0 X1 X2
       have i₂ := eq1685 X0
       grind)
    | exact superpose eq1685 eq175
    | exact resolve eq175 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1866 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (k X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq533 X1 X2 X0
       have i₂ := eq1685 X0
       grind)
    | exact superpose eq1685 eq533
    | exact resolve eq533 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1867 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (k X0 X0)) (M.op X2 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq533 X1 X0 X2
       have i₂ := eq1685 X0
       grind)
    | exact superpose eq1685 eq533
    | exact resolve eq533 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq1868 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq534 X1 X0 X2
       have i₂ := eq1685 X0
       grind)
    | exact superpose eq1685 eq534
    | exact resolve eq534 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq1871 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq560 X0 X1
       have i₂ := eq1685 X0
       grind)
    | exact superpose eq1685 eq560
    | exact resolve eq560 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq1874 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (k X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq605 X0 X1 X2
       have i₂ := eq1685 X0
       grind)
    | exact superpose eq1685 eq605
    | exact resolve eq605 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq1879 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq797 X0
       have i₂ := eq1685 X0
       grind)
    | exact superpose eq1685 eq797
    | exact resolve eq797 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq1880 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq798 X0
       have i₂ := eq1685 X0
       grind)
    | exact superpose eq1685 eq798
    | exact resolve eq798 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq1940 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) X1) = (M.op X1 (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1874 X0 X1 X2
       have i₂ := eq1685 X2
       grind)
    | exact superpose eq1685 eq1874
    | exact resolve eq1874 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1874
  have eq1943 : ∀ X0 X1 X2 : G, (M.op (M.op (k X1 X1) X2) (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1868 X0 X1 X2
       have i₂ := eq1685 X1
       grind)
    | exact superpose eq1685 eq1868
    | exact resolve eq1868 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1868
  have eq1944 : ∀ X0 X1 X2 : G, (k (M.op X1 (k X0 X0)) (M.op X2 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1867 X0 X1 X2
       have i₂ := eq1513 (M.op X1 (k X0 X0)) X2
       grind)
    | exact superpose eq1513 eq1867
    | exact resolve eq1867 eq1513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1867
  have eq1945 : ∀ X0 X1 X2 : G, (M.op (k X1 (M.op X2 X2)) (k X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1866 X0 X1 X2
       have i₂ := eq1513 X1 X2
       grind)
    | exact superpose eq1513 eq1866
    | exact resolve eq1866 eq1513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1866
  have eq1951 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) (k X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1860 X0 X1 X2
       have i₂ := eq1513 X1 X2
       grind)
    | exact superpose eq1513 eq1860
    | exact resolve eq1860 eq1513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1860
  have eq1978 : ∀ X0 X1 X2 : G, (k (M.op X1 (k X0 X0)) (k X2 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1944 X0 X1 X2
       have i₂ := eq1685 X2
       grind)
    | exact superpose eq1685 eq1944
    | exact resolve eq1944 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1944
  have eq1979 : ∀ X0 X1 X2 : G, (M.op (k X1 (k X2 X2)) (k X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1945 X0 X1 X2
       have i₂ := eq1685 X2
       grind)
    | exact superpose eq1685 eq1945
    | exact resolve eq1945 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1945
  have eq1982 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) (k X1 (k X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1951 X0 X1 X2
       have i₂ := eq1685 X2
       grind)
    | exact superpose eq1685 eq1951
    | exact resolve eq1951 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1951
  have eq2088 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X1)
       have i₂ := eq1871 (τ X1) X0
       grind)
    | exact superpose eq1871 eq34
    | exact resolve eq34 eq1871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1871
  have eq2090 : ∀ X0 X1 : G, (k X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2088 X0 X1
       have i₂ := eq14 X1
       grind)
    | exact superpose eq14 eq2088
    | exact resolve eq2088 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088
  have eq2137 : ∀ X0 X1 : G, (k X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2090 X0 X1
       have i₂ := eq1685 X0
       grind)
    | exact superpose eq1685 eq2090
    | exact resolve eq2090 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090
  have eq5355 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1529
       grind)
    | exact superpose eq1529 eq39
    | exact resolve eq39 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529
  have eq5356 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5355
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5355
    | exact resolve eq5355 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq5355
  have eq5358 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq5356
    | exact resolve eq5356 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5356
  have eq5360 : (M.op x y) = (k y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5358
       have i₂ := eq1685 y
       grind)
    | exact superpose eq1685 eq5358
    | exact resolve eq5358 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5358
  have eq5362 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq5360
       have i₂ := eq1685 x
       grind)
    | exact superpose eq1685 eq5360
    | exact resolve eq5360 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5360
  have eq6541 : ∀ X0 X1 X2 X3 X4 : G, (k X0 (k X2 X2)) = (M.op X0 (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (k X1 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq174 (k X1 X1) X3 X4 (k X0 (k X2 X2))
       have i₂ := eq1982 X1 X0 X2
       grind)
    | exact superpose eq1982 eq174
    | exact resolve eq174 eq1982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq6548 : ∀ X0 X1 X2 X3 X4 : G, (k X0 (k X2 X2)) = (M.op X0 (M.op (k (M.op X3 X3) (M.op X4 X4)) (k X1 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6541 X0 X1 X2 X3 X4
       have i₂ := eq1513 (M.op X3 X3) X4
       grind)
    | exact superpose eq1513 eq6541
    | exact resolve eq6541 eq1513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513 eq6541
  have eq6574 : ∀ X0 X1 X2 X3 X4 : G, (k X0 (k X2 X2)) = (M.op X0 (M.op (k (M.op X3 X3) (k X4 X4)) (k X1 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6548 X0 X1 X2 X3 X4
       have i₂ := eq1685 X4
       grind)
    | exact superpose eq1685 eq6548
    | exact resolve eq6548 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6548
  have eq6584 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 X3)) = (k X0 (k X2 X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq6574 X0 x X2 X3 x
       have i₂ := eq1979 x (M.op X3 X3) x
       grind)
    | exact superpose eq1979 eq6574
    | exact resolve eq6574 eq1979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1979 eq6574
  have eq6587 : ∀ X0 X2 X3 : G, (k X0 (k X2 X2)) = (M.op X0 (k X3 X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq6584 X0 X2 X3
       have i₂ := eq1685 X3
       grind)
    | exact superpose eq1685 eq6584
    | exact resolve eq6584 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6584
  have eq7441 : ∀ X0 X1 X3 : G, (M.op (k X1 X1) X0) = (k X0 (k X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1978 x (M.op (k X1 X1) X0) X3
       have i₂ := eq1943 x X1 X0
       grind)
    | exact superpose eq1943 eq1978
    | exact resolve eq1978 eq1943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1943 eq1978
  have eq8244 : ∀ X0 X1 X2 : G, (M.op X1 (k X2 X2)) = (k X1 (σ (k X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6587 X1 (σ X0) X2
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq6587
    | exact resolve eq6587 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8245 : ∀ X0 X1 X2 : G, (M.op X1 (k X2 X2)) = (k X1 (τ (k X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6587 X1 (τ X0) X2
       have i₂ := eq383 X0 X0
       grind)
    | exact superpose eq383 eq6587
    | exact resolve eq6587 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8460 : ∀ X0 : G, y = (M.op (M.op x y) (k x (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1879 x
       have i₂ := eq6587 x X0 x
       grind)
    | exact superpose eq6587 eq1879
    | exact resolve eq1879 eq6587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879
  have eq8461 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ x) (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1880 x
       have i₂ := eq6587 sF2 x x
       grind)
    | exact superpose eq6587 eq1880
    | exact resolve eq1880 eq6587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1880
  have eq10787 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) X2) = (k X2 (σ (k X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7441 X2 X1 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq7441
    | exact resolve eq7441 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10788 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) X2) = (k X2 (τ (k X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7441 X2 X1 (τ X0)
       have i₂ := eq383 X0 X0
       grind)
    | exact superpose eq383 eq7441
    | exact resolve eq7441 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq20342 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1683 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1683
  have eq20345 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (k X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20342 X0 X1
       have i₂ := eq1685 X0
       grind)
    | exact superpose eq1685 eq20342
    | (have j0 := eq20342 X0 X1
       grind)
    | exact resolve eq20342 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20342
  have eq26059 : ∀ X0 X1 : G, (k x (k X1 X1)) = (τ (M.op (σ x) (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (k X0 X0)
       have i₂ := eq8244 X0 sF2 x
       grind)
    | exact superpose eq8244 eq44
    | exact resolve eq44 eq8244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26061 : ∀ X0 X1 : G, (k y (k X1 X1)) = (τ (M.op (σ y) (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (k X0 X0)
       have i₂ := eq8244 X0 sF3 x
       grind)
    | exact superpose eq8244 eq47
    | exact resolve eq47 eq8244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8244
  have eq26714 : ∀ X0 X1 : G, (σ (M.op x (k X0 X0))) = (k (σ x) (σ (τ (k X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (τ (k X1 X1))
       have i₂ := eq8245 X1 x X0
       grind)
    | exact superpose eq8245 eq35
    | exact resolve eq35 eq8245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8245
  have eq26723 : ∀ X0 X1 : G, (σ (M.op x (k X0 X0))) = (k (σ x) (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26714 X0 X1
       have i₂ := eq14 (k X1 X1)
       grind)
    | exact superpose eq14 eq26714
    | exact resolve eq26714 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26714
  have eq32957 : ∀ X0 X1 : G, (k x (k X1 X1)) = (τ (M.op (k X0 X0) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (k X0 X0)
       have i₂ := eq10787 X0 X1 sF2
       grind)
    | exact superpose eq10787 eq44
    | exact resolve eq44 eq10787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq32959 : ∀ X0 X1 : G, (k y (k X1 X1)) = (τ (M.op (k X0 X0) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (k X0 X0)
       have i₂ := eq10787 X0 X1 sF3
       grind)
    | exact superpose eq10787 eq47
    | exact resolve eq47 eq10787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq10787
  have eq33893 : ∀ X0 X1 : G, (σ (M.op (k X0 X0) x)) = (k (σ x) (σ (τ (k X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (τ (k X1 X1))
       have i₂ := eq10788 X1 X0 x
       grind)
    | exact superpose eq10788 eq35
    | exact resolve eq35 eq10788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq33894 : ∀ X0 X1 : G, (σ (M.op (k X0 X0) y)) = (k (σ y) (σ (τ (k X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq36 (τ (k X1 X1))
       have i₂ := eq10788 X1 X0 y
       grind)
    | exact superpose eq10788 eq36
    | exact resolve eq36 eq10788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq10788
  have eq33901 : ∀ X0 X1 : G, (k (σ y) (k X1 X1)) = (σ (M.op (k X0 X0) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq33894 X0 X1
       have i₂ := eq14 (k X1 X1)
       grind)
    | exact superpose eq14 eq33894
    | exact resolve eq33894 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33894
  have eq33902 : ∀ X0 X1 : G, (k (σ x) (k X1 X1)) = (σ (M.op (k X0 X0) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq33893 X0 X1
       have i₂ := eq14 (k X1 X1)
       grind)
    | exact superpose eq14 eq33893
    | exact resolve eq33893 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33893
  have eq37817 : ∀ X0 : G, y = (M.op (M.op x y) (τ (M.op (σ x) (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq8460 x
       have i₂ := eq26059 X0 x
       grind)
    | exact superpose eq26059 eq8460
    | exact resolve eq8460 eq26059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8460 eq26059
  have eq37988 : ∀ X0 : G, y = (M.op (M.op x y) (τ (M.op (k X0 X0) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq37817 x
       have i₂ := eq1940 X0 sF2 x
       grind)
    | exact superpose eq1940 eq37817
    | exact resolve eq37817 eq1940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37817
  have eq38757 : ∀ X0 X1 : G, (τ (M.op (σ y) (k X0 X0))) = (M.op (k X1 X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq7441 y X1 x
       have i₂ := eq26061 X0 x
       grind)
    | exact superpose eq26061 eq7441
    | exact resolve eq7441 eq26061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26061
  have eq39514 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (σ (M.op x (k X0 X0)))) := by
    intro X0
    first
    | exact superpose eq26723 eq8461
    | exact resolve eq8461 eq26723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8461 eq26723
  have eq39698 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (σ (M.op (k X0 X0) x))) := by
    intro X0
    first
    | (have i₁ := eq39514 x
       have i₂ := eq1940 X0 x x
       grind)
    | exact superpose eq1940 eq39514
    | exact resolve eq39514 eq1940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1940 eq39514
  have eq82426 : ∀ X0 X1 : G, x = (M.op (k X1 X1) (τ (M.op (k X0 X0) (σ x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1982 X1 x x
       have i₂ := eq32957 X0 x
       grind)
    | exact superpose eq32957 eq1982
    | exact resolve eq1982 eq32957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32957
  have eq82640 : ∀ X0 X1 : G, y = (M.op (k X1 X1) (τ (M.op (k X0 X0) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1982 X1 y x
       have i₂ := eq32959 X0 x
       grind)
    | exact superpose eq32959 eq1982
    | exact resolve eq1982 eq32959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32959
  have eq83090 : ∀ X0 X1 : G, (σ y) = (M.op (k X1 X1) (σ (M.op (k X0 X0) y))) := by
    intro X0 X1
    first
    | exact superpose eq33901 eq1982
    | exact resolve eq1982 eq33901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83095 : ∀ X0 X2 : G, (σ (M.op (k X0 X0) y)) = (M.op (σ y) (k X2 X2)) := by
    intro X0 X2
    first
    | exact superpose eq33901 eq6587
    | exact resolve eq6587 eq33901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6587
  have eq83098 : ∀ X0 X1 : G, (σ (M.op (k X0 X0) y)) = (M.op (k X1 X1) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq33901 eq7441
    | exact resolve eq7441 eq33901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7441 eq33901
  have eq83334 : ∀ X0 X1 : G, (σ x) = (M.op (k X1 X1) (σ (M.op (k X0 X0) x))) := by
    intro X0 X1
    first
    | exact superpose eq33902 eq1982
    | exact resolve eq1982 eq33902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1982 eq33902
  have eq126113 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = (k x x) := by
    first
    | exact superpose eq5362 eq1532
    | exact resolve eq1532 eq5362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1532 eq5362
  have eq126120 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = (k x x) := by
    first
    | (have r₁ := eq126113
       have r₂ := eq27
       grind)
    | exact resolve eq126113 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126113
  have eq126124 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq126120
       have i₂ := eq1685 sF3
       grind)
    | exact superpose eq1685 eq126120
    | exact resolve eq126120 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126120
  have eq126126 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq126124
       have i₂ := eq1685 sF2
       grind)
    | exact superpose eq1685 eq126124
    | exact resolve eq126124 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126124
  have eq126579 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op (k X0 X0) x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq126126 eq83334
    | exact resolve eq83334 eq126126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126126
  have eq126597 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = (k x x) := by
    first
    | exact superpose eq39698 eq126579
    | exact resolve eq126579 eq39698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39698 eq126579
  have eq126886 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = (k x x) := by
    first
    | exact superpose eq126597 eq141
    | exact resolve eq141 eq126597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq126597
  have eq127669 : x = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y y) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq126886
    | exact resolve eq126886 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq126886
  have eq127670 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = (k x x) := by grind
  clear eq127669
  have eq128334 : ∀ X0 : G, x = (M.op (M.op x y) (τ (M.op (k X0 X0) (σ x)))) ∨ (σ x) = (σ y) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq82426 X0 y
       have i₂ := eq127670
       grind)
    | exact superpose eq127670 eq82426
    | exact resolve eq82426 eq127670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127670
  have eq128392 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq37988 eq128334
    | exact resolve eq128334 eq37988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37988 eq128334
  have eq129048 : ∀ X0 : G, (σ x) = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2137 x X0
       have i₂ := eq128392
       grind)
    | exact superpose eq128392 eq2137
    | exact resolve eq2137 eq128392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2137
  have eq129324 : ∀ X0 : G, x ≠ x ∨ x = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq20345 X0 x
       have i₂ := eq128392
       grind)
    | exact superpose eq128392 eq20345
    | (have j0 := eq20345 X0 x
       grind)
    | (have r₁ := eq20345 X0 x
       have r₂ := eq128392
       grind)
    | exact resolve eq20345 eq128392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20345
  have eq129369 : ∀ X0 : G, (M.op (k X0 X0) y) = (τ (M.op (σ y) x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq38757 x X0
       have i₂ := eq128392
       grind)
    | exact superpose eq128392 eq38757
    | exact resolve eq38757 eq128392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38757
  have eq129440 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ y) (k X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq83095 x X0
       have i₂ := eq128392
       grind)
    | exact superpose eq128392 eq83095
    | exact resolve eq83095 eq128392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83095 eq128392
  have eq129461 : ∀ X0 : G, x = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq129324 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129324
  have eq129476 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ y) (k X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq129440 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq129440
    | (have j0 := eq129440 X0
       grind)
    | exact resolve eq129440 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129440
  have eq129748 : ∀ X0 : G, (σ x) = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq129048 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq129048
    | (have j0 := eq129048 X0
       grind)
    | exact resolve eq129048 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129048
  have eq129791 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ y) (k X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq20 eq129476
    | (have j0 := eq129476 X0
       grind)
    | exact resolve eq129476 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129476
  have eq130030 : (σ (M.op x y)) = (M.op (σ y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq129461 eq129791
    | exact resolve eq129791 eq129461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129461 eq129791
  have eq135425 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op (k X0 X0) y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq83098 X0 x
       have i₂ := eq129748 x
       grind)
    | exact superpose eq129748 eq83098
    | exact resolve eq83098 eq129748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83098 eq129748
  have eq135648 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op (k X0 X0) y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq26 eq135425
    | (have j0 := eq135425 X0
       grind)
    | exact resolve eq135425 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135425
  have eq136310 : (M.op (σ x) (σ y)) = (σ (τ (M.op (σ y) x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq129369 eq135648
    | exact resolve eq135648 eq129369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129369 eq135648
  have eq136839 : (M.op (σ x) (σ y)) = (M.op (σ y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq136310
       have i₂ := eq14 (M.op sF3 x)
       grind)
    | exact superpose eq14 eq136310
    | exact resolve eq136310 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136310
  have eq137232 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq130030 eq136839
    | exact resolve eq136839 eq130030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130030 eq136839
  have eq137451 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq137232
       have r₂ := eq27
       grind)
    | exact resolve eq137232 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137232
  have eq137578 : ∀ X0 X1 : G, y = (M.op (k X0 X0) (τ (M.op (k X1 X1) (σ x)))) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq137451 eq82640
    | exact resolve eq82640 eq137451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82640 eq137451
  have eq137590 : x = y ∨ x = y := by
    first
    | exact superpose eq82426 eq137578
    | exact resolve eq137578 eq82426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82426 eq137578
  have eq137591 : x = y := by grind
  clear eq137590
  have eq137616 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq137591
       grind)
    | exact superpose eq137591 eq18
    | exact resolve eq18 eq137591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq137646 : ∀ X0 X1 : G, (σ y) = (M.op (k X0 X0) (σ (M.op (k X1 X1) x))) := by
    intro X0 X1
    first
    | (have i₁ := eq83090 X1 X0
       have i₂ := eq137591
       grind)
    | exact superpose eq137591 eq83090
    | exact resolve eq83090 eq137591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83090 eq137591
  have eq137652 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq137646 x x
       have i₂ := eq83334 x x
       grind)
    | exact superpose eq83334 eq137646
    | exact resolve eq137646 eq83334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83334 eq137646
  have eq137661 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq137616
       have i₂ := eq1685 x
       grind)
    | exact superpose eq1685 eq137616
    | exact resolve eq137616 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137616
  have eq137663 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq137652 eq26
    | exact resolve eq26 eq137652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq137652
  have eq137748 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq137663
       have i₂ := eq1685 sF2
       grind)
    | exact superpose eq1685 eq137663
    | exact resolve eq137663 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1685 eq137663
  have eq137762 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq137661
       grind)
    | exact superpose eq137661 eq39
    | exact resolve eq39 eq137661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq137661
  have eq138546 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq137762
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq137762
    | exact resolve eq137762 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq137762
  have eq138754 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq137748 eq138546
    | exact resolve eq138546 eq137748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137748 eq138546
  have eq138878 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq138754
    | exact resolve eq138754 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq138754
  have eq138966 : False := by grind
  exact eq138966
