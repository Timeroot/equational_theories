import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1480`: `x = (y ◇ x) ◇ (x ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation1480 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1480 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1480.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq576 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X1 X0) (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq607 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq576 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq608 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq607 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq707 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq608 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq710 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq707 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq707 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq707 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq707 X0 X1
       have r₂ := eq14 (M.op X1 X0) (M.op X0 X0)
       grind)
    | exact resolve eq707 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq762 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq710 X1 (τ X0)
       grind)
    | exact superpose eq710 eq19
    | (have j1 := eq710 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq765 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq710 (σ X1) (σ X0)
       grind)
    | exact superpose eq710 eq15
    | (have j1 := eq710 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq874 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq762 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq762
    | exact resolve eq762 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq919 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq874 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq874
    | (have j0 := eq874 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq874 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq1067 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq765 x y
       grind)
    | exact superpose eq765 eq16
    | (have j1 := eq765 x y
       grind)
    | exact resolve eq16 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq1099 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1067
       have i₂ := eq919 x y
       grind)
    | exact superpose eq919 eq1067
    | (have j1 := eq919 (σ x) (σ y)
       grind)
    | (have r₁ := eq1067
       have r₂ := eq919 x y
       grind)
    | (have r₁ := eq1067
       have r₂ := eq919 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1067
       have r₂ := eq919 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1067 eq919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919 eq1067
  have eq1100 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1099
  have eq1104 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1100
       grind)
    | exact superpose eq1100 eq10
    | exact resolve eq10 eq1100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq1146 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1104
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1104
    | exact resolve eq1104 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1147 : x = y := by grind
  clear eq1146
  have eq1149 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1147
       grind)
    | exact superpose eq1147 eq16
    | exact resolve eq16 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147
  have eq1150 : False := by grind
  exact eq1150

/-- `Equation1481`: `x = (y ◇ x) ◇ (x ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pyx_y_pyx_Equation1481 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1481 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1481.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq276 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
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
  have eq278 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
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
  have eq286 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq278 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq288 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq286 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq286 (M.op X1 X0) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq286 (k X0 X1) (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq286 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq286 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq296 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq287 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq287 (M.op X1 X0) X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq287 X0 (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq287 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq287 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq298 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq276
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq276 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq303 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq296 X0 X1
       have j1 := eq288 X0 X1
       grind)
    | (have r₁ := eq296 X0 X1
       have r₂ := eq288 X0 X1
       grind)
    | (have r₁ := eq296 X1 X0
       have r₂ := eq288 X0 X1
       grind)
    | (have r₁ := eq296 X1 X1
       have r₂ := eq288 (k X1 X1) X1
       grind)
    | exact resolve eq296 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq296
  have eq304 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq298
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq298
    | exact resolve eq298 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq430 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq303 X0 (τ X1)
       grind)
    | exact superpose eq303 eq17
    | (have j1 := eq303 X0 (τ X1)
       grind)
    | exact resolve eq17 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq436 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq303 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq731 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq430 (τ X0) X1
       grind)
    | exact superpose eq430 eq18
    | (have j1 := eq430 (τ X0) X1
       grind)
    | exact resolve eq18 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq430
  have eq736 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq731 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq731
    | (have j0 := eq731 X0 X1
       grind)
    | exact resolve eq731 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq749 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq736 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq736
    | (have j0 := eq736 X0 X1
       grind)
    | exact resolve eq736 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq752 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq749 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq749
    | (have j0 := eq749 X0 X1
       grind)
    | exact resolve eq749 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq817 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq752 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq752
    | (have j0 := eq752 X1 (σ X0)
       grind)
    | exact resolve eq752 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq1152 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq817 X0 X0
       have i₂ := eq303 X0 (σ X0)
       grind)
    | exact superpose eq303 eq817
    | (have j0 := eq817 X1 X0
       have j1 := eq303 X0 (σ X1)
       grind)
    | exact resolve eq817 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303 eq817
  have eq1185 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1152 X0 X1
       have j1 := eq436 (σ X1) X0
       grind)
    | (have r₁ := eq1152 X1 X1
       have r₂ := eq436 (σ X1) X1
       grind)
    | exact resolve eq1152 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436 eq1152
  have eq1308 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq1185 (σ X0) X1
       grind)
    | exact superpose eq1185 eq22
    | (have j1 := eq1185 (σ X0) X1
       grind)
    | exact resolve eq22 eq1185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1185
  have eq1316 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1308 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1308
    | (have j0 := eq1308 X0 X1
       grind)
    | exact resolve eq1308 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308
  have eq1332 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1316 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1316
    | (have j0 := eq1316 X0 X1
       grind)
    | exact resolve eq1316 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316
  have eq1341 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1332 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1332
    | (have j0 := eq1332 X0 X1
       grind)
    | exact resolve eq1332 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332
  have eq1423 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1341 x y
       grind)
    | exact superpose eq1341 eq16
    | (have j1 := eq1341 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1341 x y
       grind)
    | exact resolve eq16 eq1341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341
  have eq1444 : x = (k y x) := by grind
  clear eq1423
  have eq1732 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq304
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq304
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq304 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1733 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq1732
  have eq1734 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq1733
       have r₂ := eq12 y x
       grind)
    | exact resolve eq1733 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1733
  have eq1735 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1734
       have i₂ := eq1444
       grind)
    | exact superpose eq1444 eq1734
    | exact resolve eq1734 eq1444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734
  have eq1736 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1735
       have i₂ := eq1444
       grind)
    | exact superpose eq1444 eq1735
    | exact resolve eq1735 eq1444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1735
  have eq1737 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq304
       have i₂ := eq1736
       grind)
    | exact superpose eq1736 eq304
    | exact resolve eq304 eq1736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304 eq1736
  have eq1754 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1737
  have eq1756 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1754
       have i₂ := eq1444
       grind)
    | exact superpose eq1444 eq1754
    | exact resolve eq1754 eq1444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1754
  have eq1757 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1756
  have eq1759 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1757
       grind)
    | exact superpose eq1757 eq16
    | exact resolve eq16 eq1757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1757
  have eq1796 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1759
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq1759
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq1759 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1797 : y = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq1796
  have eq1799 : (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq1797
       have r₂ := eq12 y x
       grind)
    | exact resolve eq1797 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1797
  have eq1800 : x = (M.op x y) := by
    first
    | (have i₁ := eq1799
       have i₂ := eq1444
       grind)
    | exact superpose eq1444 eq1799
    | exact resolve eq1799 eq1444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444 eq1799
  have eq1801 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1759
       have i₂ := eq1800
       grind)
    | exact superpose eq1800 eq1759
    | exact resolve eq1759 eq1800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1759 eq1800
  have eq1820 : False := by grind
  exact eq1820

/-- `Equation1481`: `x = (y ◇ x) ◇ (x ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation1481 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1481 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1481.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  have eq53 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X0) X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq84
       have i₂ := eq68 y x
       grind)
    | exact superpose eq68 eq84
    | (have j1 := eq68 y x
       grind)
    | exact resolve eq84 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq89
    | exact resolve eq89 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq95
    | exact resolve eq95 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96
    | exact resolve eq96 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq104 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x x) ∨ (M.op x x) = (k y x) := by
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
  have eq106 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq108 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq108 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq108 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq112 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq109 x
       grind)
    | exact superpose eq109 eq43
    | exact resolve eq43 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq117 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq112
       have i₂ := eq109 sF2
       grind)
    | exact superpose eq109 eq112
    | exact resolve eq112 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq112
  have eq658 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq97 eq68
    | (have j0 := eq68 (σ y) (σ x)
       grind)
    | exact resolve eq68 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq658
    | exact resolve eq658 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq662 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq659
       have r₂ := eq27
       grind)
    | exact resolve eq659 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq664 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq662
    | exact resolve eq662 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq741 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq664 eq106
    | (have r₁ := eq106
       have r₂ := eq664
       grind)
    | exact resolve eq106 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq743 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq664 eq53
    | exact resolve eq53 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq749 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq741
  have eq794 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq749 eq97
    | exact resolve eq97 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq797 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq794
  have eq799 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq797
       have r₂ := eq27
       grind)
    | exact resolve eq797 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq802 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq799
       grind)
    | exact superpose eq799 eq104
    | (have r₁ := eq104
       have r₂ := eq799
       grind)
    | exact resolve eq104 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq803 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq117
       have i₂ := eq799
       grind)
    | exact superpose eq799 eq117
    | exact resolve eq117 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq809 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq799
       grind)
    | exact superpose eq799 eq13
    | (have j0 := eq13 X0 x
       grind)
    | exact resolve eq13 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq811 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq802
  have eq813 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq803
    | exact resolve eq803 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq891 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq84
       have i₂ := eq811
       grind)
    | exact superpose eq811 eq84
    | exact resolve eq84 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq893 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq891
    | exact resolve eq891 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq947 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq893 eq68
    | (have j0 := eq68 (σ y) (σ x)
       grind)
    | exact resolve eq68 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq950 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq947
    | exact resolve eq947 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq953 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq950
       have r₂ := eq27
       grind)
    | exact resolve eq950 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq955 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq953
    | exact resolve eq953 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq958 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq955 eq813
    | exact resolve eq813 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq972 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq958
  have eq975 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq972
       have r₂ := eq27
       grind)
    | exact resolve eq972 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq1139 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq809 X0
       grind)
    | (have r₁ := eq809 X0
       have r₂ := eq975
       grind)
    | exact resolve eq809 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809 eq975
  have eq1195 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq84
       have i₂ := eq1139 y
       grind)
    | exact superpose eq1139 eq84
    | exact resolve eq84 eq1139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139
  have eq1214 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1195
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1195
    | exact resolve eq1195 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1195
  have eq1216 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1214
    | exact resolve eq1214 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1221 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1216 eq68
    | (have j0 := eq68 (σ y) (σ x)
       grind)
    | exact resolve eq68 eq1216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216
  have eq1224 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1221
    | exact resolve eq1221 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221
  have eq1227 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1224
       have r₂ := eq27
       grind)
    | exact resolve eq1224 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224
  have eq1229 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1227
    | exact resolve eq1227 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq1291 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1229 eq813
    | exact resolve eq813 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813 eq1229
  have eq1305 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1291
  have eq1308 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1305
       have r₂ := eq27
       grind)
    | exact resolve eq1305 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305
  have eq1310 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1308 eq27
    | exact resolve eq27 eq1308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1313 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1308 eq743
    | exact resolve eq743 eq1308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq1694 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq664 eq1313
    | exact resolve eq1313 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664 eq1313
  have eq1698 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1694
  have eq1699 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1308 eq1698
    | exact resolve eq1698 eq1308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308 eq1698
  have eq1713 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1699 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1699
       grind)
    | exact resolve eq13 eq1699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1699
  have eq1714 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1713 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1713
  have eq2098 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1714 eq97
    | exact resolve eq97 eq1714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq1714
  have eq2110 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq2098
  have eq2118 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq2110
    | exact resolve eq2110 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2110
  have eq2122 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq2118
       have r₂ := eq27
       grind)
    | exact resolve eq2118 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2118
  have eq2126 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq104
       have i₂ := eq2122
       grind)
    | exact superpose eq2122 eq104
    | (have r₁ := eq104
       have r₂ := eq2122
       grind)
    | exact resolve eq104 eq2122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq2127 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq117
       have i₂ := eq2122
       grind)
    | exact superpose eq2122 eq117
    | exact resolve eq117 eq2122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq2122
  have eq2135 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq2126
  have eq2137 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq2127
    | exact resolve eq2127 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2127
  have eq2310 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq2135
       grind)
    | exact superpose eq2135 eq84
    | exact resolve eq84 eq2135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq2135
  have eq2313 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2310
    | exact resolve eq2310 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2310
  have eq2320 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2313 eq68
    | (have j0 := eq68 (σ y) (σ x)
       grind)
    | exact resolve eq68 eq2313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq2313
  have eq2321 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2320
    | exact resolve eq2320 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2320
  have eq2324 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2321
       have r₂ := eq27
       grind)
    | exact resolve eq2321 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2321
  have eq2326 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2137 eq2324
    | exact resolve eq2324 eq2137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2137 eq2324
  have eq2328 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2326
    | exact resolve eq2326 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2326
  have eq2330 : x = (M.op x y) := by
    first
    | (have r₁ := eq2328
       have r₂ := eq27
       grind)
    | exact resolve eq2328 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2328
  have eq2332 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2330 eq20
    | exact resolve eq20 eq2330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2330
  have eq2371 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2332
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2332
    | exact resolve eq2332 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2332
  have eq2377 : False := by grind
  exact eq2377

/-- `Equation1481`: `x = (y ◇ x) ◇ (x ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation1481 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1481 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1481.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  clear eq17
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2672 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq76
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq2702 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2672 X0 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq2672
    | (have j0 := eq2672 X0 X0
       grind)
    | exact resolve eq2672 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2672
  have eq4662 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (τ (k X2 X0)) = (τ (M.op X0 X2)) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq2702 X0 X2
       grind)
    | exact superpose eq2702 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq2702 X0 X2
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq2702 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq2702 X1 X1
       grind)
    | exact resolve eq12 eq2702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2702
  have eq4686 : ∀ X0 X1 X2 : G, (τ (k X2 X0)) = (τ (M.op X0 X2)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq4662 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4662
  have eq11618 : ∀ X0 X1 X2 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq4686 X0 X2 X1
       grind)
    | exact superpose eq4686 eq11
    | (have j1 := eq4686 X0 X2 X1
       grind)
    | exact resolve eq11 eq4686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4686
  have eq11753 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11618 X0 X1 X2
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq11618
    | (have j0 := eq11618 X0 X1 X1
       grind)
    | exact resolve eq11618 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11618
  have eq12006 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11753 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11753
  have eq12007 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12006 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12006
  have eq12117 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq12007 (σ X1) (σ X0)
       grind)
    | exact superpose eq12007 eq15
    | (have j1 := eq12007 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq12007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12120 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 X0
       have i₂ := eq12007 (σ X1) X0
       grind)
    | exact superpose eq12007 eq30
    | (have j1 := eq12007 (σ X1) X0
       grind)
    | exact resolve eq30 eq12007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12007
  have eq13454 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq12120 X1 X0
       grind)
    | exact superpose eq12120 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq12120 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq12120 X0 X1
       grind)
    | exact resolve eq13 eq12120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12120
  have eq13478 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (M.op X1 X1) = X1 ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq13454 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13454
  have eq13973 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12117 x y
       grind)
    | exact superpose eq12117 eq16
    | (have j1 := eq12117 x y
       grind)
    | exact resolve eq16 eq12117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14037 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq12117 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12117
  have eq14210 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14037 (τ X1) (τ X0)
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq14037
    | (have j0 := eq14037 (τ X1) (τ X0)
       grind)
    | exact resolve eq14037 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq14263 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14210 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq14210
    | (have j0 := eq14210 X0 X1
       grind)
    | exact resolve eq14210 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14210
  have eq14289 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14263 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14263
    | (have j0 := eq14263 X0 X1
       grind)
    | exact resolve eq14263 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14263
  have eq14308 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14289 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14289
    | (have j0 := eq14289 X0 X1
       grind)
    | exact resolve eq14289 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14289
  have eq14322 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14308 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq14308
    | (have j0 := eq14308 X0 X1
       grind)
    | exact resolve eq14308 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14308
  have eq70757 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = X1 ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 (σ X0))
       have i₂ := eq13478 X0 X1
       grind)
    | exact superpose eq13478 eq11
    | (have j1 := eq13478 X0 X1
       grind)
    | exact resolve eq11 eq13478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13478
  have eq70905 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = X1 ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq70757 X0 X1
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq70757
    | (have j0 := eq70757 X0 X1
       grind)
    | exact resolve eq70757 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq70757
  have eq70988 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq70905 X0 X1
       have j1 := eq12 (σ X0) X1
       grind)
    | (have r₁ := eq70905 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq70905 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70905
  have eq71203 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq70988 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq70988
    | exact resolve eq70988 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70988
  have eq72643 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13973
       have i₂ := eq71203 y x
       grind)
    | exact superpose eq71203 eq13973
    | (have j1 := eq71203 y x
       grind)
    | exact resolve eq13973 eq71203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13973
  have eq72645 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq71203 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71203
  have eq72647 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by grind
  clear eq72643
  have eq73911 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq72645 (σ y) (σ x)
       have i₂ := eq72647
       grind)
    | exact superpose eq72647 eq72645
    | (have j0 := eq72645 (σ y) (σ x)
       grind)
    | (have r₁ := eq72645 (σ y) (σ x)
       have r₂ := eq72647
       grind)
    | exact resolve eq72645 eq72647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72647
  have eq73912 : (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by grind
  clear eq73911
  have eq73915 : y = (k y x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq73912
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq73912
    | exact resolve eq73912 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73912
  have eq74689 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14037 x y
       have i₂ := eq73915
       grind)
    | exact superpose eq73915 eq14037
    | (have j0 := eq14037 x y
       grind)
    | (have r₁ := eq14037 x y
       have r₂ := eq73915
       grind)
    | exact resolve eq14037 eq73915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73915
  have eq74719 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq74689
  have eq74731 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq14037 x y
       grind)
    | (have r₁ := eq74719
       have r₂ := eq14037 x y
       grind)
    | exact resolve eq74719 eq14037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14037 eq74719
  have eq74743 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq74731
       grind)
    | exact superpose eq74731 eq16
    | exact resolve eq16 eq74731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74750 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq72645 (σ y) (σ x)
       have i₂ := eq74731
       grind)
    | exact superpose eq74731 eq72645
    | (have j0 := eq72645 (σ y) (σ x)
       grind)
    | (have r₁ := eq72645 (σ y) (σ x)
       have r₂ := eq74731
       grind)
    | exact resolve eq72645 eq74731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72645 eq74731
  have eq74751 : (σ y) = (k (σ y) (σ x)) := by grind
  clear eq74750
  have eq74754 : (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq74751
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq74751
    | exact resolve eq74751 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74751
  have eq75435 : (k y x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq74754
       grind)
    | exact superpose eq74754 eq10
    | exact resolve eq10 eq74754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74754
  have eq75754 : y = (k y x) := by
    first
    | (have i₁ := eq75435
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq75435
    | exact resolve eq75435 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75435
  have eq76536 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14322 y x
       have i₂ := eq75754
       grind)
    | exact superpose eq75754 eq14322
    | (have j0 := eq14322 y x
       grind)
    | (have r₁ := eq14322 y x
       have r₂ := eq75754
       grind)
    | exact resolve eq14322 eq75754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14322 eq75754
  have eq76562 : y = (M.op x y) := by grind
  clear eq76536
  have eq76584 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq74743
       have i₂ := eq76562
       grind)
    | exact superpose eq76562 eq74743
    | exact resolve eq74743 eq76562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74743 eq76562
  have eq76594 : False := by grind
  exact eq76594

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_y_pyx_y_pyx_Equation1483 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1483 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
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
  have eq78 : x ≠ (M.op x y) ∨ x = (M.op y x) ∨ x = (k y x) := by
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
  have eq79 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq96 y x
       grind)
    | exact superpose eq96 eq75
    | (have j1 := eq96 y x
       grind)
    | exact resolve eq75 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107
    | exact resolve eq107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq119
    | exact resolve eq119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122 eq96
    | (have j0 := eq96 (σ y) (σ x)
       grind)
    | exact resolve eq96 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq126
       have r₂ := eq27
       grind)
    | exact resolve eq126 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq131 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq129
    | exact resolve eq129 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq133 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131 eq27
    | exact resolve eq27 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq596 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131 eq79
    | (have r₁ := eq79
       have r₂ := eq131
       grind)
    | exact resolve eq79 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq131
  have eq597 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq596
  have eq600 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq597 eq122
    | exact resolve eq122 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq604 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq600
  have eq609 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq604
       have r₂ := eq133
       grind)
    | exact resolve eq604 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq604
  have eq617 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq609 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq609
       grind)
    | exact resolve eq13 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq623 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq617
  have eq628 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq623
    | exact resolve eq623 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq698 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq628 eq122
    | exact resolve eq122 eq628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq628
  have eq701 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq698
  have eq705 : x = (M.op x y) := by
    first
    | (have r₁ := eq701
       have r₂ := eq27
       grind)
    | exact resolve eq701 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq707 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq705 eq20
    | exact resolve eq20 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq713 : x ≠ x ∨ x = (M.op y x) ∨ x = (k y x) := by
    first
    | exact superpose eq705 eq78
    | (have r₁ := eq78
       have r₂ := eq705
       grind)
    | exact resolve eq78 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq719 : x = (k y x) ∨ x = (M.op y x) := by grind
  clear eq713
  have eq725 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq707
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq707
    | exact resolve eq707 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq726 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq725 eq26
    | exact resolve eq26 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1927 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq719
       grind)
    | exact superpose eq719 eq75
    | exact resolve eq75 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq1934 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq725 eq1927
    | exact resolve eq1927 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1927
  have eq1936 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1934
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1934
    | exact resolve eq1934 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1934
  have eq1937 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq725 eq1936
    | exact resolve eq1936 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1936
  have eq1940 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1937 eq96
    | (have j0 := eq96 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq96 eq1937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1937
  have eq1941 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq1940
  have eq1943 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq726 eq1941
    | exact resolve eq1941 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1941
  have eq1946 : x = (M.op y x) := by
    first
    | (have r₁ := eq1943
       have r₂ := eq27
       grind)
    | exact resolve eq1943 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1943
  have eq1956 : x ≠ x ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1946
       grind)
    | exact superpose eq1946 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1946
       grind)
    | exact resolve eq13 eq1946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1946
  have eq1968 : (M.op x y) = (k y x) := by grind
  clear eq1956
  have eq1969 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1968
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1968
    | exact resolve eq1968 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1968
  have eq1974 : x = (k y x) := by
    first
    | exact superpose eq705 eq1969
    | exact resolve eq1969 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705 eq1969
  have eq2027 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq1974
       grind)
    | exact superpose eq1974 eq75
    | exact resolve eq75 eq1974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq1974
  have eq2034 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq725 eq2027
    | exact resolve eq2027 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2027
  have eq2036 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2034
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2034
    | exact resolve eq2034 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2034
  have eq2037 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq725 eq2036
    | exact resolve eq2036 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725 eq2036
  have eq2074 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2037 eq96
    | (have j0 := eq96 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq96 eq2037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq2037
  have eq2075 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq2074
  have eq2077 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq726 eq2075
    | exact resolve eq2075 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726 eq2075
  have eq2080 : False := by grind
  exact eq2080

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation1483 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1483 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X2))) = X0 := by
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
  have eq55 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X0) (M.op X0 (M.op X1 x))
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : y ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (k y x) := by
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
  have eq76 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq93 y x
       grind)
    | exact superpose eq93 eq72
    | (have j1 := eq93 y x
       grind)
    | exact resolve eq72 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq104
    | exact resolve eq104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq116
    | exact resolve eq116 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq118
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq118
    | exact resolve eq118 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq119 eq93
    | (have j0 := eq93 (σ y) (σ x)
       grind)
    | exact resolve eq93 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq122
    | exact resolve eq122 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq126 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq123
       have r₂ := eq27
       grind)
    | exact resolve eq123 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq128 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq126
    | exact resolve eq126 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq130 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq128 eq27
    | exact resolve eq27 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq450 : ∀ X0 : G, x = (M.op (M.op (M.op X0 y) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq55 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55
    | (have j0 := eq55 y X0 x
       grind)
    | exact resolve eq55 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq548 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq128 eq76
    | (have r₁ := eq76
       have r₂ := eq128
       grind)
    | exact resolve eq76 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq128
  have eq549 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq548
  have eq552 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq549 eq119
    | exact resolve eq119 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq556 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq552
  have eq561 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq556
       have r₂ := eq130
       grind)
    | exact resolve eq556 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq556
  have eq570 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq561 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq561
       grind)
    | exact resolve eq13 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq576 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq570 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq1413 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq576 eq119
    | exact resolve eq119 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq576
  have eq1416 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1413
  have eq1423 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1416
    | exact resolve eq1416 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1416
  have eq1425 : y = (M.op x y) := by
    first
    | (have r₁ := eq1423
       have r₂ := eq27
       grind)
    | exact resolve eq1423 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1423
  have eq1428 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1425 eq20
    | exact resolve eq20 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1433 : y ≠ y ∨ x = (M.op x x) ∨ y = (k y x) := by
    first
    | exact superpose eq1425 eq75
    | (have r₁ := eq75
       have r₂ := eq1425
       grind)
    | exact resolve eq75 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq1439 : y = (k y x) ∨ x = (M.op x x) := by grind
  clear eq1433
  have eq1445 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1428
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1428
    | exact resolve eq1428 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428
  have eq1447 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1445 eq26
    | exact resolve eq26 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1685 : ∀ X0 : G, x = (M.op (M.op (M.op X0 y) x) y) := by
    intro X0
    first
    | exact superpose eq1425 eq450
    | exact resolve eq450 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq1689 : x = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq1685 (M.op (M.op x y) x)
       have i₂ := eq1685 x
       grind)
    | exact superpose eq1685 eq1685
    | exact resolve eq1685 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1685
  have eq2089 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq1439
       grind)
    | exact superpose eq1439 eq72
    | exact resolve eq72 eq1439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq1439
  have eq2096 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1445 eq2089
    | exact resolve eq2089 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2089
  have eq2098 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2096
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2096
    | exact resolve eq2096 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2096
  have eq2099 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1445 eq2098
    | exact resolve eq2098 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2098
  have eq2242 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2099 eq93
    | (have j0 := eq93 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq93 eq2099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2099
  have eq2243 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) := by grind
  clear eq2242
  have eq2245 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1447 eq2243
    | exact resolve eq2243 eq1447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2243
  have eq2248 : x = (M.op x x) := by
    first
    | (have r₁ := eq2245
       have r₂ := eq27
       grind)
    | exact resolve eq2245 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2245
  have eq2253 : x = (M.op x y) := by
    first
    | (have i₁ := eq1689
       have i₂ := eq2248
       grind)
    | exact superpose eq2248 eq1689
    | exact resolve eq1689 eq2248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1689
  have eq2259 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq2248
       grind)
    | exact superpose eq2248 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq2248
       grind)
    | exact resolve eq13 eq2248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2248
  have eq2269 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq2259 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2259
  have eq2275 : x = (M.op x y) := by
    first
    | (have i₁ := eq2253
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2253
    | exact resolve eq2253 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2253
  have eq2278 : x = y := by
    first
    | exact superpose eq1425 eq2275
    | exact resolve eq2275 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275
  have eq2285 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2278
       grind)
    | exact superpose eq2278 eq24
    | exact resolve eq24 eq2278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2278
  have eq2324 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1445 eq2285
    | exact resolve eq2285 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445 eq2285
  have eq2335 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2324
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2324
    | exact resolve eq2324 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2324
  have eq2381 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2335 eq1447
    | exact resolve eq1447 eq2335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447
  have eq2434 : (k (σ (M.op x y)) (σ x)) = (σ (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq138
       have i₂ := eq2269 sF0
       grind)
    | exact superpose eq2269 eq138
    | exact resolve eq138 eq2269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq2269
  have eq2440 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1425 eq2434
    | exact resolve eq2434 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425 eq2434
  have eq2445 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2335 eq2440
    | exact resolve eq2440 eq2335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2335 eq2440
  have eq2448 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2445
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2445
    | exact resolve eq2445 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2445
  have eq2451 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq2448
    | exact resolve eq2448 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2448
  have eq2456 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2451 eq93
    | (have j0 := eq93 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq93 eq2451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq2451
  have eq2457 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2456
  have eq2459 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2381 eq2457
    | exact resolve eq2457 eq2381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2381 eq2457
  have eq2462 : False := by grind
  exact eq2462

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation1483 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1483 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq96 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq96 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq13
    | (have j0 := eq13 (k (σ X0) (σ X1)) (M.op (σ X0) (σ X1))
       have j1 := eq96 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq96 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq96 X0 X1
       grind)
    | exact resolve eq13 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq300 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq289 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq301 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq300 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq307 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq301 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq301
    | (have j0 := eq301 X0 X1
       grind)
    | exact resolve eq301 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq308 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq307 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq643 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq308 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq308
    | exact resolve eq308 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq308 x y
       grind)
    | exact superpose eq308 eq16
    | (have j1 := eq308 x y
       grind)
    | exact resolve eq16 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq677 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq643 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq643
    | (have j0 := eq643 X0 X1
       grind)
    | exact resolve eq643 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq643
  have eq762 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq677 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq677
    | exact resolve eq677 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq909 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq649
       have i₂ := eq762 x y
       grind)
    | exact superpose eq762 eq649
    | (have j1 := eq762 (σ x) (σ y)
       grind)
    | (have r₁ := eq649
       have r₂ := eq762 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq649
       have r₂ := eq762 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq649 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq762
  have eq912 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq909
  have eq1014 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq912
       grind)
    | exact superpose eq912 eq10
    | exact resolve eq10 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq1052 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1014
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1014
    | exact resolve eq1014 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq1053 : x = y := by grind
  clear eq1052
  have eq1055 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1053
       grind)
    | exact superpose eq1053 eq16
    | exact resolve eq16 eq1053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053
  have eq1056 : False := by grind
  exact eq1056

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation1483 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1483 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  clear eq28
  have eq697 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1144 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq1152 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq1161 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1144 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq1144
    | (have j0 := eq1144 X0 X1
       grind)
    | exact resolve eq1144 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144
  have eq2610 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1161 x y
       grind)
    | exact superpose eq1161 eq16
    | (have j1 := eq1161 x y
       grind)
    | exact resolve eq16 eq1161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2648 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1161 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161
  have eq8957 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1152 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1152
    | exact resolve eq1152 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152
  have eq9048 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8957 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8957
    | (have j0 := eq8957 X0 X1
       grind)
    | exact resolve eq8957 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8957
  have eq16214 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq2610
       have i₂ := eq9048 y x
       grind)
    | exact superpose eq9048 eq2610
    | (have j1 := eq9048 y x
       grind)
    | (have r₁ := eq2610
       have r₂ := eq9048 y x
       grind)
    | (have r₁ := eq2610
       have r₂ := eq9048 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2610
       have r₂ := eq9048 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2610 eq9048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2610 eq9048
  have eq16215 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq16214
  have eq18422 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2648 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq2648
    | (have j0 := eq2648 (τ X1) (τ X0)
       grind)
    | exact resolve eq2648 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq18480 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18422 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq18422
    | (have j0 := eq18422 X0 X1
       grind)
    | exact resolve eq18422 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18422
  have eq18515 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18480 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq18480
    | (have j0 := eq18480 X0 X1
       grind)
    | exact resolve eq18480 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18480
  have eq18547 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18515 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18515
    | (have j0 := eq18515 X0 X1
       grind)
    | exact resolve eq18515 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18515
  have eq18573 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18547 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq18547
    | (have j0 := eq18547 X0 X1
       grind)
    | exact resolve eq18547 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18547
  have eq18593 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18573 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq18573
    | (have j0 := eq18573 X0 X1
       grind)
    | exact resolve eq18573 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq18573
  have eq18612 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18593 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq18593
    | (have j0 := eq18593 X0 X1
       grind)
    | exact resolve eq18593 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18593
  have eq18625 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18612 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18612
    | (have j0 := eq18612 X0 X1
       grind)
    | exact resolve eq18612 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18612
  have eq46433 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16215
       grind)
    | exact superpose eq16215 eq16
    | exact resolve eq16 eq16215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16215
  have eq46434 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq46433
       have r₂ := eq22 x
       grind)
    | exact resolve eq46433 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46433
  have eq46437 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq46434
       grind)
    | exact superpose eq46434 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq46434
       grind)
    | exact resolve eq13 eq46434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46434
  have eq46480 : x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq46437
  have eq59420 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46480
       grind)
    | exact superpose eq46480 eq16
    | exact resolve eq16 eq46480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46480
  have eq59421 : (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq59420
       have r₂ := eq22 x
       grind)
    | exact resolve eq59420 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59420
  have eq59428 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2648 x y
       have i₂ := eq59421
       grind)
    | exact superpose eq59421 eq2648
    | (have j0 := eq2648 x y
       grind)
    | exact resolve eq2648 eq59421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2648 eq59421
  have eq59460 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq59428
  have eq59461 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq59460
  have eq59469 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq59461
       grind)
    | exact superpose eq59461 eq16
    | exact resolve eq16 eq59461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59478 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq697 x (σ y)
       have i₂ := eq59461
       grind)
    | exact superpose eq59461 eq697
    | (have j0 := eq697 x (σ y)
       grind)
    | (have r₁ := eq697 x (σ y)
       have r₂ := eq59461
       grind)
    | exact resolve eq697 eq59461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697 eq59461
  have eq59546 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
  clear eq59478
  have eq59547 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
  clear eq59546
  have eq59557 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq59547
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq59547
    | exact resolve eq59547 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59547
  have eq59568 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq59557
       grind)
    | exact superpose eq59557 eq10
    | exact resolve eq10 eq59557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59557
  have eq59799 : x = y ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq59568
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq59568
    | exact resolve eq59568 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59568
  have eq59801 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq59799
       grind)
    | exact superpose eq59799 eq16
    | exact resolve eq16 eq59799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59799
  have eq59802 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq59801
       have r₂ := eq22 x
       grind)
    | exact resolve eq59801 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59801
  have eq59818 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq59802
       grind)
    | exact superpose eq59802 eq10
    | exact resolve eq10 eq59802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59802
  have eq60050 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq59818
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq59818
    | exact resolve eq59818 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59818
  have eq60082 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq18625 y x
       have i₂ := eq60050
       grind)
    | exact superpose eq60050 eq18625
    | (have j0 := eq18625 y x
       grind)
    | (have r₁ := eq18625 y x
       have r₂ := eq60050
       grind)
    | exact resolve eq18625 eq60050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18625 eq60050
  have eq60091 : x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq60082
  have eq60095 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq60091
       grind)
    | exact superpose eq60091 eq16
    | exact resolve eq16 eq60091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60091
  have eq60098 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq60095
       have r₂ := eq22 x
       grind)
    | exact resolve eq60095 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60095
  have eq60694 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq59469
       have i₂ := eq60098
       grind)
    | exact superpose eq60098 eq59469
    | exact resolve eq59469 eq60098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59469
  have eq60743 : (σ x) = (σ y) := by grind
  clear eq60694
  have eq60744 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq60743
       grind)
    | exact superpose eq60743 eq16
    | exact resolve eq16 eq60743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60743
  have eq60979 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq60744
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq60744
    | exact resolve eq60744 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq60744
  have eq60980 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq60979
       have i₂ := eq60098
       grind)
    | exact superpose eq60098 eq60979
    | exact resolve eq60979 eq60098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60098 eq60979
  have eq60981 : False := by grind
  exact eq60981
