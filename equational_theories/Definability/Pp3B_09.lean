import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_pxx_pyx_Equation1486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq37 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq37 (σ X0)
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq39
    | exact resolve eq39 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq39
  have eq61 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq61
    | (have j0 := eq61 X0 X1
       grind)
    | exact resolve eq61 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq66
    | exact resolve eq66 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq294 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq278 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq278
    | (have j0 := eq278 X0 X1
       grind)
    | exact resolve eq278 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq300 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq294 X0 X1
       have j1 := eq90 X1 X0
       grind)
    | (have r₁ := eq294 X1 X0
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq294 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq294 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq294
  have eq306 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq300 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq300
    | exact resolve eq300 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq300 (σ X1) X0
       grind)
    | exact superpose eq300 eq15
    | (have j1 := eq300 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq320 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq306 X0 (τ X1)
       grind)
    | exact superpose eq306 eq18
    | (have j1 := eq306 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq306
  have eq681 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq320 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq320
    | exact resolve eq320 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq712 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq681 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq681
    | (have j0 := eq681 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq681 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq1438 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq311 x y
       grind)
    | exact superpose eq311 eq16
    | (have j1 := eq311 x y
       grind)
    | exact resolve eq16 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq1525 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1438
       have i₂ := eq712 y x
       grind)
    | exact superpose eq712 eq1438
    | (have j1 := eq712 (σ x) (σ y)
       grind)
    | (have r₁ := eq1438
       have r₂ := eq712 y x
       grind)
    | (have r₁ := eq1438
       have r₂ := eq712 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1438
       have r₂ := eq712 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1438 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712 eq1438
  have eq1526 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1525
  have eq1530 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1526
       grind)
    | exact superpose eq1526 eq10
    | exact resolve eq10 eq1526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526
  have eq1573 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1530
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1530
    | exact resolve eq1530 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1530
  have eq1574 : x = y := by grind
  clear eq1573
  have eq1582 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1574
       grind)
    | exact superpose eq1574 eq16
    | exact resolve eq16 eq1574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1574
  have eq1583 : False := by grind
  exact eq1583

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_x_pyx_Equation1486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq37 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq37 (σ X0)
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq39
    | exact resolve eq39 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq39
  have eq61 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq61
    | (have j0 := eq61 X0 X1
       grind)
    | exact resolve eq61 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq66
    | exact resolve eq66 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq294 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq278 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq278
    | (have j0 := eq278 X0 X1
       grind)
    | exact resolve eq278 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq300 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq294 X0 X1
       have j1 := eq90 X1 X0
       grind)
    | (have r₁ := eq294 X1 X0
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq294 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq294 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq294
  have eq306 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq300 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq300
    | exact resolve eq300 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq300 (σ X1) X0
       grind)
    | exact superpose eq300 eq15
    | (have j1 := eq300 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq320 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq306 X0 (τ X1)
       grind)
    | exact superpose eq306 eq18
    | (have j1 := eq306 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq306
  have eq681 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq320 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq320
    | exact resolve eq320 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq712 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq681 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq681
    | (have j0 := eq681 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq681 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq1438 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq311 x y
       grind)
    | exact superpose eq311 eq16
    | (have j1 := eq311 x y
       grind)
    | exact resolve eq16 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq1525 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1438
       have i₂ := eq712 y x
       grind)
    | exact superpose eq712 eq1438
    | (have j1 := eq712 (σ x) (σ y)
       grind)
    | (have r₁ := eq1438
       have r₂ := eq712 y x
       grind)
    | (have r₁ := eq1438
       have r₂ := eq712 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1438
       have r₂ := eq712 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1438 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712 eq1438
  have eq1526 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1525
  have eq1530 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1526
       grind)
    | exact superpose eq1526 eq10
    | exact resolve eq10 eq1526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526
  have eq1573 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1530
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1530
    | exact resolve eq1530 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1530
  have eq1574 : x = y := by grind
  clear eq1573
  have eq1582 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1574
       grind)
    | exact superpose eq1574 eq16
    | exact resolve eq16 eq1574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1574
  have eq1583 : False := by grind
  exact eq1583

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxy_pyx_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq91 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq519 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq12 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq531 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq520 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq536 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq531 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq531 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq531 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq531 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq537 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq519 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq519 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq519 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq545 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq536 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq536
    | (have j0 := eq536 X0 X1
       grind)
    | exact resolve eq536 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq546 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq545 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq547 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq537 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq537
    | (have j0 := eq537 X0 X1
       grind)
    | exact resolve eq537 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq548 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq547 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq553 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq548 X0 X1
       have j1 := eq546 X0 X1
       grind)
    | (have r₁ := eq548 X0 X1
       have r₂ := eq546 X0 X1
       grind)
    | exact resolve eq548 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq548
  have eq554 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq553 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq553
    | exact resolve eq553 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq553 x y
       grind)
    | exact superpose eq553 eq16
    | exact resolve eq16 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq688 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq554 X0 (τ X1)
       grind)
    | exact superpose eq554 eq18
    | exact resolve eq18 eq554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq554
  have eq703 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq688 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq688
    | exact resolve eq688 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq710 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq703 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq703
    | exact resolve eq703 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq722 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq565
       have i₂ := eq710 x y
       grind)
    | exact superpose eq710 eq565
    | exact resolve eq565 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565 eq710
  have eq723 : False := by grind
  exact eq723

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_pyy_pyx_pyy_pyx_Equation1486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq289 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq289 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq289 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq289 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq301 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq290 (σ X0)
       grind)
    | exact superpose eq290 eq15
    | exact resolve eq15 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq307 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq290 (τ X0)
       grind)
    | exact superpose eq290 eq31
    | exact resolve eq31 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq314 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq307 X0
       have i₂ := eq290 X0
       grind)
    | exact superpose eq290 eq307
    | exact resolve eq307 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq320 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq301 X0
       have i₂ := eq290 X0
       grind)
    | exact superpose eq290 eq301
    | exact resolve eq301 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290 eq301
  have eq805 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq822 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq805 X0 X1
       have i₂ := eq320 X0
       grind)
    | exact superpose eq320 eq805
    | (have j0 := eq805 X0 X1
       grind)
    | exact resolve eq805 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq5497 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq822 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq822
    | exact resolve eq822 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq5613 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5497 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq5497
    | (have j0 := eq5497 X0 X1
       grind)
    | exact resolve eq5497 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5497
  have eq5616 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5613 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq5613 X1 (M.op (τ X1) (τ X1))
       have r₂ := eq12 (σ (M.op (τ X1) (τ X1))) X1
       grind)
    | (have r₁ := eq5613 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq5613 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5613
  have eq5617 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5616 X0 X1
       have i₂ := eq314 X0
       grind)
    | exact superpose eq314 eq5616
    | (have j0 := eq5616 X0 X1
       grind)
    | exact resolve eq5616 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314 eq5616
  have eq5618 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5617 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq5617
    | (have j0 := eq5617 X0 X1
       grind)
    | exact resolve eq5617 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5617
  have eq5619 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5618 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5618
    | exact resolve eq5618 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5625 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq5618 (σ X0) X1
       grind)
    | exact superpose eq5618 eq15
    | (have j1 := eq5618 (σ X0) X1
       grind)
    | exact resolve eq15 eq5618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5618
  have eq5649 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5625 X0 X1
       have i₂ := eq320 X0
       grind)
    | exact superpose eq320 eq5625
    | (have j0 := eq5625 X0 X1
       grind)
    | exact resolve eq5625 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5625
  have eq5678 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq5619 (τ X1) X0
       grind)
    | exact superpose eq5619 eq17
    | (have j1 := eq5619 (τ X1) X0
       grind)
    | exact resolve eq17 eq5619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq5619
  have eq5809 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5678 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5678
    | exact resolve eq5678 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5678
  have eq5860 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5809 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5809
    | (have j0 := eq5809 X0 X1
       grind)
    | exact resolve eq5809 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5809
  have eq11630 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5649 x y
       grind)
    | exact superpose eq5649 eq16
    | (have j1 := eq5649 x y
       grind)
    | exact resolve eq16 eq5649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11774 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5649 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5649
  have eq11806 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq11630
       have i₂ := eq5860 y x
       grind)
    | exact superpose eq5860 eq11630
    | (have j1 := eq5860 y x
       grind)
    | (have r₁ := eq11630
       have r₂ := eq5860 y x
       grind)
    | exact resolve eq11630 eq5860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11630
  have eq11807 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq11806
  have eq11811 : y ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq11807
       grind)
    | exact superpose eq11807 eq12
    | exact resolve eq12 eq11807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11812 : (M.op x x) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq11807
       grind)
    | exact superpose eq11807 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq11807
       grind)
    | exact resolve eq13 eq11807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11807
  have eq11830 : y = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq11812
  have eq11831 : (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq11811
       have r₂ := eq11830
       grind)
    | exact resolve eq11811 eq11830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11811 eq11830
  have eq11857 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq11774 x y
       have i₂ := eq11831
       grind)
    | exact superpose eq11831 eq11774
    | (have j0 := eq11774 x y
       grind)
    | exact resolve eq11774 eq11831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11774 eq11831
  have eq11897 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq11857
  have eq11898 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq11897
  have eq12161 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11898
       grind)
    | exact superpose eq11898 eq16
    | exact resolve eq16 eq11898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12164 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq11898
       grind)
    | exact superpose eq11898 eq12
    | exact resolve eq12 eq11898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12165 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq11898
       grind)
    | exact superpose eq11898 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq11898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11898
  have eq12184 : (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq12165
       have r₂ := eq320 x
       grind)
    | exact resolve eq12165 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12165
  have eq12185 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12164
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq12164
    | exact resolve eq12164 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12164
  have eq12187 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12184
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq12184
    | exact resolve eq12184 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12184
  have eq12188 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12187
       have i₂ := eq320 x
       grind)
    | exact superpose eq320 eq12187
    | exact resolve eq12187 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320 eq12187
  have eq12189 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq12188
       have r₂ := eq12185
       grind)
    | exact resolve eq12188 eq12185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12185 eq12188
  have eq12197 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq5860 y x
       have i₂ := eq12189
       grind)
    | exact superpose eq12189 eq5860
    | (have j0 := eq5860 y x
       grind)
    | exact resolve eq5860 eq12189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5860 eq12189
  have eq12259 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq12197
       have r₂ := eq12161
       grind)
    | exact resolve eq12197 eq12161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12197
  have eq12276 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq12161
       have i₂ := eq12259
       grind)
    | exact superpose eq12259 eq12161
    | exact resolve eq12161 eq12259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12161 eq12259
  have eq12298 : False := by grind
  exact eq12298

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pyx_y_pyx_Equation1486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq82 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq31
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq31 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq81 x y
       grind)
    | exact superpose eq81 eq16
    | (have j1 := eq81 x y
       grind)
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq500 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq501 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1221 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ X1) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq501 X1 (τ X0)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq501
    | (have j0 := eq501 X1 (τ X0)
       grind)
    | exact resolve eq501 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq501
  have eq1241 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ X0 ∨ (σ X1) = (M.op (σ X1) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ X1) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1221 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1221
    | (have j0 := eq1221 X0 X1
       grind)
    | exact resolve eq1221 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221
  have eq1252 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ X1) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1241 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1241
    | (have j0 := eq1241 X0 X1
       grind)
    | exact resolve eq1241 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq1262 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ X0 ∨ (σ X1) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1252 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1252
    | (have j0 := eq1252 X0 X1
       grind)
    | exact resolve eq1252 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252
  have eq3912 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (M.op X1 (σ X0)) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) X0
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq12
    | (have j1 := eq82 X1 X0
       grind)
    | (have r₁ := eq12 (σ X1) X0
       have r₂ := eq82 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq82 (σ X1) X1
       grind)
    | exact resolve eq12 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3924 : ∀ X0 X1 : G, (σ X1) ≠ X0 ∨ (M.op X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq3926 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) X1) ∨ (M.op X1 (σ X0)) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq3912 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3912
  have eq4257 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3924 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3924
    | (have r₁ := eq3924 X0 (τ X0)
       have r₂ := eq11 X0
       grind)
    | (have r₁ := eq3924 (σ (τ (σ X1))) X1
       have r₂ := eq11 (σ X1)
       grind)
    | exact resolve eq3924 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3924
  have eq4278 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4257 X0 X1
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq4257
    | (have j0 := eq4257 X0 X1
       grind)
    | (have r₁ := eq4257 (k (τ X1) (τ X0)) (τ (k X1 X0))
       have r₂ := eq35 X0 X1
       grind)
    | (have r₁ := eq4257 (τ (k X1 X0)) (k (τ X1) (τ X0))
       have r₂ := eq35 X0 X1
       grind)
    | exact resolve eq4257 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4257
  have eq4279 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4278 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4278
  have eq4347 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4279 X0
       grind)
    | exact superpose eq4279 eq11
    | (have j1 := eq4279 X0
       grind)
    | exact resolve eq11 eq4279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4279
  have eq4456 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4347 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4347
    | (have j0 := eq4347 X0
       grind)
    | exact resolve eq4347 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4347
  have eq4470 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4456 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq4456 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq4456 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4456
  have eq4513 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4470 (σ X0)
       grind)
    | exact superpose eq4470 eq15
    | exact resolve eq15 eq4470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4582 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4513 X0
       have i₂ := eq4470 X0
       grind)
    | exact superpose eq4470 eq4513
    | exact resolve eq4513 eq4470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4470 eq4513
  have eq101104 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3926 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3926
    | exact resolve eq3926 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101149 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (M.op X1 (σ X0)) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq3926 X0 X1
       grind)
    | exact superpose eq3926 eq31
    | (have j1 := eq3926 X0 X1
       grind)
    | exact resolve eq31 eq3926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3926
  have eq101397 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (M.op X1 (σ X0)) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq101149 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq101149
    | (have j0 := eq101149 X0 X1
       grind)
    | exact resolve eq101149 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101149
  have eq101408 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq101104 X0 X1
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq101104
    | (have j0 := eq101104 X0 X1
       grind)
    | exact resolve eq101104 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101104
  have eq101700 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq101408 X1 X0
       grind)
    | exact superpose eq101408 eq11
    | (have j1 := eq101408 X1 X0
       grind)
    | exact resolve eq11 eq101408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101408
  have eq101895 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq101700 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq101700
    | (have j0 := eq101700 X0 X1
       grind)
    | exact resolve eq101700 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101700
  have eq102160 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq101895 (τ X0) X1
       grind)
    | exact superpose eq101895 eq18
    | (have j1 := eq101895 (τ X0) X1
       grind)
    | exact resolve eq18 eq101895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq101895
  have eq102917 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (M.op X1 (σ (τ X0))) = X1 ∨ (τ (k X0 X1)) = (τ (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq101397 (τ X1) X0
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq101397
    | (have j0 := eq101397 (τ X0) X1
       grind)
    | exact resolve eq101397 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq101397
  have eq103208 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X1 (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq102917 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq102917
    | (have j0 := eq102917 X0 X1
       grind)
    | exact resolve eq102917 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102917
  have eq103312 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq103208 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq103208
    | (have j0 := eq103208 X0 X1
       grind)
    | exact resolve eq103208 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103208
  have eq103870 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (M.op X1 X0) = X1 ∨ (τ X0) ≠ (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq103312 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103312
  have eq104576 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op (σ X1) X0)) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (τ X0) = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1
       have i₂ := eq103870 X0 (σ X1)
       grind)
    | exact superpose eq103870 eq25
    | (have j1 := eq103870 X0 (σ X1)
       grind)
    | exact resolve eq25 eq103870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq104584 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (τ X0) ≠ (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq103870 X0 X1
       grind)
    | exact superpose eq103870 eq11
    | (have j1 := eq103870 X0 X1
       grind)
    | exact resolve eq11 eq103870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103870
  have eq104788 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq104584 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq104584
    | (have j0 := eq104584 X0 X1
       grind)
    | exact resolve eq104584 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104584
  have eq105024 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq104788 (σ X1) (σ X0)
       have i₂ := eq81 X0 X1
       grind)
    | exact superpose eq81 eq104788
    | (have j0 := eq104788 (σ X0) (σ X1)
       have j1 := eq81 X1 X0
       grind)
    | exact resolve eq104788 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq104788
  have eq105075 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq105024 X0 X1
       have j1 := eq500 X1 X0
       grind)
    | (have r₁ := eq105024 X1 X0
       have r₂ := eq500 X0 X1
       grind)
    | exact resolve eq105024 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105024
  have eq105171 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq105075 X0 X1
       have j1 := eq1262 (σ X0) X1
       grind)
    | (have r₁ := eq105075 X0 X1
       have r₂ := eq1262 (σ X0) X1
       grind)
    | exact resolve eq105075 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262 eq105075
  have eq105214 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq105171 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq105171
    | (have j0 := eq105171 X0 X1
       grind)
    | exact resolve eq105171 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105171
  have eq105239 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq105214 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq105214
    | (have j0 := eq105214 X0 X1
       grind)
    | exact resolve eq105214 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105214
  have eq125636 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq102160 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq102160
    | exact resolve eq102160 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102160
  have eq126058 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq125636 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq125636
    | (have j0 := eq125636 X0 X1
       grind)
    | exact resolve eq125636 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125636
  have eq126714 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq490
       have i₂ := eq126058 x y
       grind)
    | exact superpose eq126058 eq490
    | (have j1 := eq126058 x y
       grind)
    | (have r₁ := eq490
       have r₂ := eq126058 x y
       grind)
    | exact resolve eq490 eq126058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq126884 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq126714
  have eq126947 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq105239 y x
       grind)
    | (have r₁ := eq126884
       have r₂ := eq105239 y x
       grind)
    | exact resolve eq126884 eq105239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105239 eq126884
  have eq127595 : x ≠ y ∨ x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq126947
       grind)
    | exact superpose eq126947 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq126947
       grind)
    | exact resolve eq12 eq126947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127596 : x ≠ x ∨ x = (k y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq126947
       grind)
    | exact superpose eq126947 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq126947
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq126947
       grind)
    | exact resolve eq13 eq126947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126947
  have eq127632 : x = (k y x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq127596
  have eq127646 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq127595
       have r₂ := eq127632
       grind)
    | exact resolve eq127595 eq127632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127595 eq127632
  have eq127654 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq500 x y
       have i₂ := eq127646
       grind)
    | exact superpose eq127646 eq500
    | (have j0 := eq500 x y
       grind)
    | exact resolve eq500 eq127646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500 eq127646
  have eq127706 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq127654
  have eq127707 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq127706
  have eq128339 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq127707
       grind)
    | exact superpose eq127707 eq16
    | exact resolve eq16 eq127707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128341 : (τ (σ y)) ≠ (τ (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq104576 (σ y) x
       have i₂ := eq127707
       grind)
    | exact superpose eq127707 eq104576
    | (have j0 := eq104576 (σ y) x
       grind)
    | exact resolve eq104576 eq127707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104576
  have eq128360 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq127707
       grind)
    | exact superpose eq127707 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq127707
       grind)
    | exact resolve eq12 eq127707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128398 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq127707
  have eq128403 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq128360
  have eq128406 : (σ x) = (σ y) ∨ (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq128341
  have eq128420 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq128403
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq128403
    | exact resolve eq128403 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128403
  have eq128432 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq128406
       have r₂ := eq128398
       grind)
    | exact resolve eq128406 eq128398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128398 eq128406
  have eq128444 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq128432
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq128432
    | exact resolve eq128432 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128432
  have eq129738 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq128420
       grind)
    | exact superpose eq128420 eq16
    | exact resolve eq16 eq128420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129758 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq128420
       grind)
    | exact superpose eq128420 eq12
    | exact resolve eq12 eq128420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129759 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq128420
       grind)
    | exact superpose eq128420 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq128420
       grind)
    | exact resolve eq13 eq128420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128420
  have eq129795 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq129759
  have eq129811 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq129795
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq129795
    | exact resolve eq129795 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129795
  have eq129812 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq129758
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq129758
    | exact resolve eq129758 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129758
  have eq129834 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq129812
       have r₂ := eq129811
       grind)
    | exact resolve eq129812 eq129811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129811 eq129812
  have eq130484 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq129834
       grind)
    | exact superpose eq129834 eq10
    | exact resolve eq10 eq129834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130665 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq129834
  have eq130739 : y = (k y x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq130484
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq130484
    | exact resolve eq130484 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130484
  have eq131419 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq130739
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq130739
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq130739 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130739
  have eq131464 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq131419
  have eq132156 : y ≠ y ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq131464
       grind)
    | exact superpose eq131464 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq131464
       grind)
    | exact resolve eq12 eq131464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132194 : x ≠ y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq131464
  have eq132199 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k y x) := by grind
  clear eq132156
  have eq132856 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k y x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq129738
       have i₂ := eq132199
       grind)
    | exact superpose eq132199 eq129738
    | (have r₁ := eq129738
       have r₂ := eq132199
       grind)
    | exact resolve eq129738 eq132199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132896 : (σ y) = (σ (k y x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k y x) := by grind
  clear eq132856
  have eq132910 : y = (k y x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq132896
       have r₂ := eq129738
       grind)
    | exact resolve eq132896 eq129738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129738 eq132896
  have eq133618 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq132910
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq132910
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq132910 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132910
  have eq133663 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq133618
  have eq135866 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128339
       have i₂ := eq133663
       grind)
    | exact superpose eq133663 eq128339
    | (have r₁ := eq128339
       have r₂ := eq133663
       grind)
    | exact resolve eq128339 eq133663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133663
  have eq135914 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq135866
  have eq135928 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq135914
       have r₂ := eq128339
       grind)
    | exact resolve eq135914 eq128339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128339 eq135914
  have eq135939 : x ≠ y ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq135928
       grind)
    | exact superpose eq135928 eq12
    | exact resolve eq12 eq135928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135940 : x ≠ x ∨ x = (k y x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq135928
       grind)
    | exact superpose eq135928 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq135928
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq135928
       grind)
    | exact resolve eq13 eq135928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135928
  have eq135976 : x = (k y x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq135940
  have eq135991 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq135939
       have r₂ := eq135976
       grind)
    | exact resolve eq135939 eq135976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135939 eq135976
  have eq136677 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq128444
       have i₂ := eq135991
       grind)
    | exact superpose eq135991 eq128444
    | exact resolve eq128444 eq135991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128444 eq135991
  have eq136735 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq136677
  have eq136743 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq136735
       grind)
    | exact superpose eq136735 eq16
    | exact resolve eq16 eq136735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136735
  have eq136814 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq136743
       have r₂ := eq4582 x
       grind)
    | exact resolve eq136743 eq4582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4582 eq136743
  have eq137549 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq136814
       grind)
    | exact superpose eq136814 eq16
    | exact resolve eq16 eq136814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137570 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq136814
       grind)
    | exact superpose eq136814 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq136814
       grind)
    | exact resolve eq13 eq136814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136814
  have eq137606 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq137570
  have eq137622 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq137606
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq137606
    | exact resolve eq137606 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137606
  have eq137644 : (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq137622
       have r₂ := eq130665
       grind)
    | exact resolve eq137622 eq130665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130665 eq137622
  have eq137664 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq137549
       have i₂ := eq132199
       grind)
    | exact superpose eq132199 eq137549
    | (have r₁ := eq137549
       have r₂ := eq132199
       grind)
    | exact resolve eq137549 eq132199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132199
  have eq137669 : (σ (M.op x y)) = (σ x) ∨ y = (k y x) := by grind
  clear eq137664
  have eq137671 : y = (k y x) := by
    first
    | (have r₁ := eq137669
       have r₂ := eq137549
       grind)
    | exact resolve eq137669 eq137549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137669
  have eq137763 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq137644
       grind)
    | exact superpose eq137644 eq10
    | exact resolve eq10 eq137644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137644
  have eq138155 : x = (k y x) := by
    first
    | (have i₁ := eq137763
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq137763
    | exact resolve eq137763 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137763
  have eq138341 : x = y := by
    first
    | (have i₁ := eq137671
       have i₂ := eq138155
       grind)
    | exact superpose eq138155 eq137671
    | exact resolve eq137671 eq138155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137671
  have eq138385 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq126058 x y
       have i₂ := eq138155
       grind)
    | exact superpose eq138155 eq126058
    | (have j0 := eq126058 x y
       grind)
    | exact resolve eq126058 eq138155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126058 eq138155
  have eq138395 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq138385
       have r₂ := eq132194
       grind)
    | exact resolve eq138385 eq132194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132194 eq138385
  have eq138397 : x = (M.op x y) := by
    first
    | (have r₁ := eq138395
       have r₂ := eq137549
       grind)
    | exact resolve eq138395 eq137549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138395
  have eq138398 : x = (M.op x x) := by
    first
    | (have i₁ := eq138397
       have i₂ := eq138341
       grind)
    | exact superpose eq138341 eq138397
    | exact resolve eq138397 eq138341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138397
  have eq138429 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq137549
       have i₂ := eq138341
       grind)
    | exact superpose eq138341 eq137549
    | exact resolve eq137549 eq138341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137549 eq138341
  have eq138453 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq138429
       have i₂ := eq138398
       grind)
    | exact superpose eq138398 eq138429
    | exact resolve eq138429 eq138398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138398 eq138429
  have eq138454 : False := by grind
  exact eq138454

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pxy_pxx_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X2 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq65 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) ≠ X0 ∨ (k (M.op X0 (M.op X2 X2)) (M.op X1 X0)) = (M.op (M.op X0 (M.op X2 X2)) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 (M.op X2 X2)) (M.op X1 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X0 (M.op X2 X2)) (M.op X1 X0)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = X2 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    grind
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    grind
  have eq73 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq71 X0
       have j1 := eq65 (M.op X0 X0) (M.op X0 X0) X0
       grind)
    | (have r₁ := eq71 x
       have r₂ := eq65 (M.op x x) x x
       grind)
    | exact resolve eq71 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq71
  have eq74 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq9 (M.op X0 X0) (M.op X0 X0) X0
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq100 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq105 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq746 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq74 X0
       have i₂ := eq69 X0 X0 X0
       grind)
    | exact superpose eq69 eq74
    | (have j1 := eq69 X0 x x
       grind)
    | exact resolve eq74 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq74
  have eq755 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq746 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq773 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq755 (σ X0)
       grind)
    | exact superpose eq755 eq15
    | exact resolve eq15 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq792 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq773 X0
       have i₂ := eq755 X0
       grind)
    | exact superpose eq755 eq773
    | exact resolve eq773 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755 eq773
  have eq4495 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq100 x y
       grind)
    | exact superpose eq100 eq16
    | (have j1 := eq100 x y
       grind)
    | exact resolve eq16 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq12833 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq105
    | exact resolve eq105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq12895 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12833 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq12833
    | (have j0 := eq12833 X0 X1
       grind)
    | exact resolve eq12833 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12833
  have eq42630 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq4495
       have i₂ := eq12895 y x
       grind)
    | exact superpose eq12895 eq4495
    | (have j1 := eq12895 (σ x) (σ y)
       grind)
    | (have r₁ := eq4495
       have r₂ := eq12895 y x
       grind)
    | (have r₁ := eq4495
       have r₂ := eq12895 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq4495
       have r₂ := eq12895 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq4495 eq12895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42631 : x = y ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq42630
  have eq42633 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42631
       grind)
    | exact superpose eq42631 eq16
    | exact resolve eq16 eq42631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42631
  have eq42634 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq42633
       have r₂ := eq792 x
       grind)
    | exact resolve eq42633 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42633
  have eq42636 : x ≠ x ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq42634
       grind)
    | exact superpose eq42634 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq42634
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq42634
       grind)
    | exact resolve eq12 eq42634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42634
  have eq42659 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq42636
  have eq42660 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq4495
       have i₂ := eq42659
       grind)
    | exact superpose eq42659 eq4495
    | exact resolve eq4495 eq42659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4495 eq42659
  have eq42661 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq42660
  have eq42662 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq42661
  have eq42668 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq42662
       grind)
    | exact superpose eq42662 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq42662
       grind)
    | exact resolve eq12 eq42662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42662
  have eq42691 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq42668
  have eq42696 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq42691
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq42691
    | exact resolve eq42691 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42691
  have eq42700 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42696
       grind)
    | exact superpose eq42696 eq16
    | exact resolve eq16 eq42696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42696
  have eq42732 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq42700
       have i₂ := eq12895 y x
       grind)
    | exact superpose eq12895 eq42700
    | (have j1 := eq12895 (σ x) (σ y)
       grind)
    | (have r₁ := eq42700
       have r₂ := eq12895 y x
       grind)
    | (have r₁ := eq42700
       have r₂ := eq12895 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq42700
       have r₂ := eq12895 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq42700 eq12895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12895
  have eq42733 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq42732
  have eq42737 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42733
       grind)
    | exact superpose eq42733 eq16
    | exact resolve eq16 eq42733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42733
  have eq42738 : x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq42737
       have r₂ := eq792 x
       grind)
    | exact resolve eq42737 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42737
  have eq42740 : x ≠ x ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq42738
       grind)
    | exact superpose eq42738 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq42738
       grind)
    | exact resolve eq12 eq42738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42738
  have eq42763 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq42740
  have eq42764 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq42700
       have i₂ := eq42763
       grind)
    | exact superpose eq42763 eq42700
    | exact resolve eq42700 eq42763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42700 eq42763
  have eq42768 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq42764
  have eq42769 : (σ x) = (σ y) := by grind
  clear eq42768
  have eq42770 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42769
       grind)
    | exact superpose eq42769 eq16
    | exact resolve eq16 eq42769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42771 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq42769
       grind)
    | exact superpose eq42769 eq10
    | exact resolve eq10 eq42769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42769
  have eq42849 : x = y := by
    first
    | (have i₁ := eq42771
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq42771
    | exact resolve eq42771 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42771
  have eq42850 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq42770
       have i₂ := eq792 x
       grind)
    | exact superpose eq792 eq42770
    | exact resolve eq42770 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792 eq42770
  have eq42853 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq42850
       have i₂ := eq42849
       grind)
    | exact superpose eq42849 eq42850
    | exact resolve eq42850 eq42849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42849 eq42850
  have eq42854 : False := by grind
  exact eq42854

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pxy_pxy_pxx_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq57 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq57 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq57 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq60 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq58 (σ X0)
       grind)
    | exact superpose eq58 eq15
    | exact resolve eq15 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq58 (τ X0)
       grind)
    | exact superpose eq58 eq18
    | exact resolve eq18 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq63
    | exact resolve eq63 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq69 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq60
    | exact resolve eq60 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq72 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq66
    | exact resolve eq66 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq66
  have eq83 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq89
    | (have j0 := eq89 X0 X1
       grind)
    | exact resolve eq89 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq368 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq95 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq95
    | exact resolve eq95 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq409 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq368 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq368
    | (have j0 := eq368 X0 X1
       grind)
    | exact resolve eq368 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq368
  have eq413 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq409 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq409 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq409 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq416 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq413 X0 X1
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq413
    | (have j0 := eq413 X0 X1
       grind)
    | exact resolve eq413 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq975 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq416 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq416
    | exact resolve eq416 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq986 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq416 (σ X0) X1
       grind)
    | exact superpose eq416 eq15
    | (have j1 := eq416 (σ X0) X1
       grind)
    | exact resolve eq15 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq999 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq986 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq986
    | (have j0 := eq986 X0 X1
       grind)
    | exact resolve eq986 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq986
  have eq1015 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq975 (τ X1) X0
       grind)
    | exact superpose eq975 eq18
    | (have j1 := eq975 (τ X1) X0
       grind)
    | exact resolve eq18 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq975
  have eq5108 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1015 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1015
    | exact resolve eq1015 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015
  have eq5164 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5108 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5108
    | (have j0 := eq5108 X0 X1
       grind)
    | exact resolve eq5108 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5108
  have eq15356 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq999 x y
       grind)
    | exact superpose eq999 eq16
    | (have j1 := eq999 x y
       grind)
    | exact resolve eq16 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15508 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq999 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999
  have eq15726 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq15356
       have i₂ := eq5164 y x
       grind)
    | exact superpose eq5164 eq15356
    | (have j1 := eq5164 y x
       grind)
    | (have r₁ := eq15356
       have r₂ := eq5164 y x
       grind)
    | exact resolve eq15356 eq5164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5164 eq15356
  have eq15727 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq15726
  have eq15732 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ y = (M.op y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq15727
       grind)
    | exact superpose eq15727 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq15727
       grind)
    | exact resolve eq13 eq15727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15751 : y = (M.op y x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq15732
  have eq15890 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15508 (τ X0) (τ X1)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq15508
    | (have j0 := eq15508 (τ X0) (τ X1)
       grind)
    | exact resolve eq15508 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq15973 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15890 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq15890
    | (have j0 := eq15890 X0 X1
       grind)
    | exact resolve eq15890 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15890
  have eq16012 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15973 X0 X1
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq15973
    | (have j0 := eq15973 X0 X1
       grind)
    | exact resolve eq15973 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15973
  have eq16044 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16012 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq16012
    | (have j0 := eq16012 X0 X1
       grind)
    | exact resolve eq16012 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16012
  have eq16069 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16044 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16044
    | (have j0 := eq16044 X0 X1
       grind)
    | exact resolve eq16044 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16044
  have eq16088 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16069 X0 X1
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq16069
    | (have j0 := eq16069 X0 X1
       grind)
    | exact resolve eq16069 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq16069
  have eq61888 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq15751
       grind)
    | exact superpose eq15751 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq15751
       grind)
    | exact resolve eq12 eq15751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15751
  have eq61912 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
  clear eq61888
  have eq251179 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq61912
       grind)
    | exact superpose eq61912 eq16
    | exact resolve eq16 eq61912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61912
  have eq251255 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq251179
       have i₂ := eq15727
       grind)
    | exact superpose eq15727 eq251179
    | exact resolve eq251179 eq15727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15727 eq251179
  have eq251256 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq251255
  have eq251257 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by grind
  clear eq251256
  have eq251813 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq83 x (σ y)
       have i₂ := eq251257
       grind)
    | exact superpose eq251257 eq83
    | (have j0 := eq83 x (σ y)
       grind)
    | (have r₁ := eq83 x (σ y)
       have r₂ := eq251257
       grind)
    | exact resolve eq83 eq251257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq251880 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k x y) = (M.op x x) := by grind
  clear eq251813
  have eq251884 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq251880
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq251880
    | exact resolve eq251880 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251880
  have eq318049 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq251884
       grind)
    | exact superpose eq251884 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq251884
       grind)
    | exact resolve eq12 eq251884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251884
  have eq318104 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by grind
  clear eq318049
  have eq318128 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq318104
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq318104
    | exact resolve eq318104 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318104
  have eq1475648 : (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq251257
       have i₂ := eq318128
       grind)
    | exact superpose eq318128 eq251257
    | exact resolve eq251257 eq318128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251257 eq318128
  have eq1475886 : (k x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq1475648
  have eq1479718 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq15508 x y
       have i₂ := eq1475886
       grind)
    | exact superpose eq1475886 eq15508
    | (have j0 := eq15508 x y
       grind)
    | (have r₁ := eq15508 x y
       have r₂ := eq1475886
       grind)
    | exact resolve eq15508 eq1475886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1479721 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16088 x y
       have i₂ := eq1475886
       grind)
    | exact superpose eq1475886 eq16088
    | (have j0 := eq16088 x y
       grind)
    | (have r₁ := eq16088 x y
       have r₂ := eq1475886
       grind)
    | exact resolve eq16088 eq1475886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475886
  have eq1479958 : (M.op x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq1479721
  have eq1479960 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq1479718
  have eq1479969 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq15508 x y
       grind)
    | (have r₁ := eq1479960
       have r₂ := eq15508 x y
       grind)
    | exact resolve eq1479960 eq15508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15508 eq1479960
  have eq1479985 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1479969
       grind)
    | exact superpose eq1479969 eq16
    | exact resolve eq16 eq1479969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479969
  have eq1493516 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1479985
       have i₂ := eq1479958
       grind)
    | exact superpose eq1479958 eq1479985
    | exact resolve eq1479985 eq1479958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479958
  have eq1493583 : (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq1493516
  have eq1493655 : (k x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq1493583
       grind)
    | exact superpose eq1493583 eq10
    | exact resolve eq10 eq1493583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493583
  have eq1494279 : (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq1493655
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq1493655
    | exact resolve eq1493655 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493655
  have eq1498300 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16088 x y
       have i₂ := eq1494279
       grind)
    | exact superpose eq1494279 eq16088
    | (have j0 := eq16088 x y
       grind)
    | (have r₁ := eq16088 x y
       have r₂ := eq1494279
       grind)
    | exact resolve eq16088 eq1494279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16088 eq1494279
  have eq1498537 : (M.op x y) = (M.op x x) := by grind
  clear eq1498300
  have eq1498555 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1479985
       have i₂ := eq1498537
       grind)
    | exact superpose eq1498537 eq1479985
    | exact resolve eq1479985 eq1498537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479985 eq1498537
  have eq1498622 : False := by grind
  exact eq1498622

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pxy_y_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq269 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq269 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq277 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq276 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq385 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq277 X0 X1
       grind)
    | exact superpose eq277 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq277 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq277 X0 X1
       grind)
    | exact resolve eq13 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq391 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq277 (σ y) (σ x)
       grind)
    | exact superpose eq277 eq16
    | (have j1 := eq277 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq394 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq385 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq395 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq391
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq391
    | exact resolve eq391 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq397 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq394 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq394 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq394 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq401 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq397 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq397
    | exact resolve eq397 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq397 X1 (τ X0)
       grind)
    | exact superpose eq397 eq17
    | (have j1 := eq397 X1 (τ X0)
       grind)
    | exact resolve eq17 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq429 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq397 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1569 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq423 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq423
    | exact resolve eq423 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1591 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq423 X1 (τ X0)
       grind)
    | exact superpose eq423 eq18
    | (have j1 := eq423 X1 (τ X0)
       grind)
    | exact resolve eq18 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq423
  have eq1596 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1591 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1591
    | (have j0 := eq1591 X0 X1
       grind)
    | exact resolve eq1591 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1591
  have eq1609 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1569 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1569
    | (have j0 := eq1569 X0 X1
       grind)
    | exact resolve eq1569 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569
  have eq1610 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1596 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1596
    | (have j0 := eq1596 X0 X1
       grind)
    | exact resolve eq1596 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596
  have eq1613 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1610 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1610
    | (have j0 := eq1610 X0 X1
       grind)
    | exact resolve eq1610 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1610
  have eq1671 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1613 X0 X1
       have i₂ := eq397 X0 X1
       grind)
    | exact superpose eq397 eq1613
    | (have j0 := eq1613 X1 X0
       have j1 := eq397 X1 X0
       grind)
    | exact resolve eq1613 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq1613
  have eq1729 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1671 X0 X1
       have j1 := eq429 X0 X1
       grind)
    | (have r₁ := eq1671 X0 X1
       have r₂ := eq429 X0 X1
       grind)
    | exact resolve eq1671 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429 eq1671
  have eq1769 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq1729 X1 (σ X0)
       grind)
    | exact superpose eq1729 eq22
    | (have j1 := eq1729 X1 (σ X0)
       grind)
    | exact resolve eq22 eq1729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1729
  have eq1802 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1769 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1769
    | (have j0 := eq1769 X0 X1
       grind)
    | exact resolve eq1769 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1769
  have eq1821 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1802 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1802
    | (have j0 := eq1802 X0 X1
       grind)
    | exact resolve eq1802 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1802
  have eq2515 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1821 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1821
    | exact resolve eq1821 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1821
  have eq3805 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq395
       have i₂ := eq277 y x
       grind)
    | exact superpose eq277 eq395
    | (have j1 := eq277 y x
       grind)
    | exact resolve eq395 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3807 : (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq3805
  have eq4029 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq401 x y
       have i₂ := eq3807
       grind)
    | exact superpose eq3807 eq401
    | (have j0 := eq401 x y
       grind)
    | exact resolve eq401 eq3807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401 eq3807
  have eq4038 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq4029
       have r₂ := eq395
       grind)
    | exact resolve eq4029 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395 eq4029
  have eq4040 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq4038
       have r₂ := eq16
       grind)
    | exact resolve eq4038 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4038
  have eq4043 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4040
       grind)
    | exact superpose eq4040 eq16
    | exact resolve eq16 eq4040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4040
  have eq4091 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4043
       have i₂ := eq2515 x y
       grind)
    | exact superpose eq2515 eq4043
    | (have j1 := eq2515 x y
       grind)
    | exact resolve eq4043 eq2515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2515
  have eq4095 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq4043
       have i₂ := eq1609 x y
       grind)
    | exact superpose eq1609 eq4043
    | (have j1 := eq1609 x y
       grind)
    | (have r₁ := eq4043
       have r₂ := eq1609 x y
       grind)
    | exact resolve eq4043 eq1609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1609 eq4043
  have eq4096 : y = (k x y) := by grind
  clear eq4095
  have eq4102 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have r₁ := eq4091
       have r₂ := eq16
       grind)
    | exact resolve eq4091 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4091
  have eq4112 : (σ y) ≠ (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq4102
       have i₂ := eq277 y x
       grind)
    | exact superpose eq277 eq4102
    | (have j1 := eq277 y x
       grind)
    | exact resolve eq4102 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq4114 : (M.op x y) = (k x y) := by grind
  clear eq4112
  have eq4115 : y = (M.op x y) := by
    first
    | (have i₁ := eq4114
       have i₂ := eq4096
       grind)
    | exact superpose eq4096 eq4114
    | exact resolve eq4114 eq4096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4096 eq4114
  have eq4117 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq4102
       have i₂ := eq4115
       grind)
    | exact superpose eq4115 eq4102
    | exact resolve eq4102 eq4115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4102 eq4115
  have eq4141 : False := by grind
  exact eq4141
