import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pyx_x_pyx_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq61 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq66 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
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
  have eq188 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
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
  have eq200 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq188 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq188
    | (have j0 := eq188 X0 X1
       grind)
    | exact resolve eq188 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq207 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq200 X0 X1
       have j1 := eq90 X1 X0
       grind)
    | (have r₁ := eq200 X1 X0
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq200 (M.op X1 (σ X0)) (M.op X0 X0)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq200 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq200
  have eq244 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq207 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq207
    | exact resolve eq207 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq207 (σ X1) X0
       grind)
    | exact superpose eq207 eq15
    | (have j1 := eq207 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq272 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq244 X0 (τ X1)
       grind)
    | exact superpose eq244 eq18
    | (have j1 := eq244 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq244
  have eq664 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq272 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq272
    | exact resolve eq272 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq695 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq664 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq664
    | (have j0 := eq664 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq664 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq1405 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq249 x y
       grind)
    | exact superpose eq249 eq16
    | (have j1 := eq249 x y
       grind)
    | exact resolve eq16 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq1437 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1405
       have i₂ := eq695 y x
       grind)
    | exact superpose eq695 eq1405
    | (have j1 := eq695 (σ x) (σ y)
       grind)
    | (have r₁ := eq1405
       have r₂ := eq695 y x
       grind)
    | (have r₁ := eq1405
       have r₂ := eq695 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1405
       have r₂ := eq695 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1405 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695 eq1405
  have eq1438 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1437
  have eq1442 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1438
       grind)
    | exact superpose eq1438 eq10
    | exact resolve eq10 eq1438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438
  have eq1485 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1442
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1442
    | exact resolve eq1442 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442
  have eq1486 : x = y := by grind
  clear eq1485
  have eq1548 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1486
       grind)
    | exact superpose eq1486 eq16
    | exact resolve eq16 eq1486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1486
  have eq1549 : False := by grind
  exact eq1549

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,Y) else if X = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pyy_pyy_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq72 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq67 (τ X0)
       grind)
    | exact superpose eq67 eq32
    | exact resolve eq32 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq72 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq72
    | exact resolve eq72 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
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
  have eq97 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ X0)
       have i₂ := eq81 X0
       grind)
    | exact superpose eq81 eq12
    | exact resolve eq12 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq974 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq982 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq991 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq974 X0 X1
       have i₂ := eq81 X1
       grind)
    | exact superpose eq81 eq974
    | (have j0 := eq974 X0 X1
       grind)
    | exact resolve eq974 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq5626 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq991 x y
       grind)
    | exact superpose eq991 eq16
    | (have j1 := eq991 x y
       grind)
    | exact resolve eq16 eq991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5656 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq991 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq26078 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq982 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq982
    | exact resolve eq982 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982
  have eq26223 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26078 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq26078
    | (have j0 := eq26078 X0 X1
       grind)
    | exact resolve eq26078 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26078
  have eq38929 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq5626
       have i₂ := eq26223 x y
       grind)
    | exact superpose eq26223 eq5626
    | (have j1 := eq26223 x y
       grind)
    | (have r₁ := eq5626
       have r₂ := eq26223 x y
       grind)
    | (have r₁ := eq5626
       have r₂ := eq26223 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5626
       have r₂ := eq26223 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5626 eq26223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5626 eq26223
  have eq38930 : x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq38929
  have eq48083 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5656 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq5656
    | (have j0 := eq5656 (τ X0) (τ X1)
       grind)
    | exact resolve eq5656 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq48204 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (τ (M.op X1 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq48083 X0 X1
       have i₂ := eq79 X1
       grind)
    | exact superpose eq79 eq48083
    | (have j0 := eq48083 X0 X1
       grind)
    | exact resolve eq48083 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48083
  have eq48275 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq48204 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq48204
    | (have j0 := eq48204 X0 X1
       grind)
    | exact resolve eq48204 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48204
  have eq48338 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq48275 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq48275
    | (have j0 := eq48275 X0 X1
       grind)
    | exact resolve eq48275 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48275
  have eq48392 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq48338 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq48338
    | (have j0 := eq48338 X0 X1
       grind)
    | exact resolve eq48338 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48338
  have eq48440 : ∀ X0 X1 : G, (σ (τ (M.op X1 X1))) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq48392 X0 X1
       have i₂ := eq79 X1
       grind)
    | exact superpose eq79 eq48392
    | (have j0 := eq48392 X0 X1
       grind)
    | exact resolve eq48392 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq48392
  have eq48485 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (M.op X1 X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq48440 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48440
    | (have j0 := eq48440 X0 X1
       grind)
    | exact resolve eq48440 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48440
  have eq48524 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq48485 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq48485
    | (have j0 := eq48485 X0 X1
       grind)
    | exact resolve eq48485 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48485
  have eq48561 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48524 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq48524
    | (have j0 := eq48524 X0 X1
       grind)
    | exact resolve eq48524 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48524
  have eq48592 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48561 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48561
    | (have j0 := eq48561 X0 X1
       grind)
    | exact resolve eq48561 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48561
  have eq95792 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38930
       grind)
    | exact superpose eq38930 eq16
    | exact resolve eq16 eq38930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38930
  have eq95793 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq95792
       have r₂ := eq81 x
       grind)
    | exact resolve eq95792 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95792
  have eq95797 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq97 y (σ x)
       have i₂ := eq95793
       grind)
    | exact superpose eq95793 eq97
    | (have j0 := eq97 y (σ x)
       grind)
    | (have r₁ := eq97 y (σ x)
       have r₂ := eq95793
       grind)
    | exact resolve eq97 eq95793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq95793
  have eq95825 : (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq95797
  have eq95828 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq95825
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq95825
    | exact resolve eq95825 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95825
  have eq95830 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq95828
       grind)
    | exact superpose eq95828 eq10
    | exact resolve eq10 eq95828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95828
  have eq96040 : x = y ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq95830
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq95830
    | exact resolve eq95830 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95830
  have eq96042 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq96040
       grind)
    | exact superpose eq96040 eq16
    | exact resolve eq16 eq96040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96040
  have eq96043 : (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq96042
       have r₂ := eq81 x
       grind)
    | exact resolve eq96042 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96042
  have eq96052 : (k x y) = (τ (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq96043
       grind)
    | exact superpose eq96043 eq10
    | exact resolve eq10 eq96043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96043
  have eq96268 : (k x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq96052
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq96052
    | exact resolve eq96052 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96052
  have eq96269 : (k x y) = (M.op y y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq96268
       have r₂ := eq12 x y
       grind)
    | exact resolve eq96268 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96268
  have eq96276 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5656 x y
       have i₂ := eq96269
       grind)
    | exact superpose eq96269 eq5656
    | (have j0 := eq5656 x y
       grind)
    | exact resolve eq5656 eq96269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5656
  have eq96293 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq48592 x y
       have i₂ := eq96269
       grind)
    | exact superpose eq96269 eq48592
    | (have j0 := eq48592 x y
       grind)
    | (have r₁ := eq48592 x y
       have r₂ := eq96269
       grind)
    | exact resolve eq48592 eq96269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48592 eq96269
  have eq96303 : x = y ∨ (M.op x y) = (M.op y y) := by grind
  clear eq96293
  have eq96304 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
  clear eq96276
  have eq96307 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq96303
       grind)
    | exact superpose eq96303 eq16
    | exact resolve eq16 eq96303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96303
  have eq96309 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq96307
       have r₂ := eq81 x
       grind)
    | exact resolve eq96307 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96307
  have eq108385 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq96304
       grind)
    | exact superpose eq96304 eq16
    | exact resolve eq16 eq96304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96304
  have eq108426 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq108385
       have i₂ := eq96309
       grind)
    | exact superpose eq96309 eq108385
    | exact resolve eq108385 eq96309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96309 eq108385
  have eq108427 : (σ x) = (σ y) := by grind
  clear eq108426
  have eq108429 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq108427
       grind)
    | exact superpose eq108427 eq16
    | exact resolve eq16 eq108427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108432 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq108427
       grind)
    | exact superpose eq108427 eq10
    | exact resolve eq10 eq108427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108427
  have eq108700 : x = y := by
    first
    | (have i₁ := eq108432
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq108432
    | exact resolve eq108432 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108432
  have eq108701 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq108429
       have i₂ := eq81 x
       grind)
    | exact superpose eq81 eq108429
    | exact resolve eq108429 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq108429
  have eq108706 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq108701
       have i₂ := eq108700
       grind)
    | exact superpose eq108700 eq108701
    | exact resolve eq108701 eq108700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108700 eq108701
  have eq108707 : False := by grind
  exact eq108707

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_pyx_pyx_pxx_pyx_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq25 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq25 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
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
    | (have r₁ := eq13 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
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
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq38 (k X1 X1) X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq38 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq44 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq44 (k X1 X1) X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq44 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq56 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq46 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq60 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq52
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       have j1 := eq59 X0 X1
       grind)
    | (have r₁ := eq60 X0 X1
       have r₂ := eq59 X0 X1
       grind)
    | exact resolve eq60 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq60
  have eq108 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq112 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq108 X0 X1
       have j1 := eq63 X1 X0
       grind)
    | (have r₁ := eq108 X1 X0
       have r₂ := eq63 X0 X1
       grind)
    | (have r₁ := eq108 X0 X0
       have r₂ := eq63 X0 X0
       grind)
    | exact resolve eq108 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq108
  have eq389 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq112 (σ X1) (σ X0)
       grind)
    | exact superpose eq112 eq15
    | exact resolve eq15 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq389 X0 X1
       have i₂ := eq112 X1 X0
       grind)
    | exact superpose eq112 eq389
    | exact resolve eq389 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq389
  have eq396 : False := by grind
  exact eq396

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_x_pyx_x_pyx_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq267 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
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
  have eq268 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
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
  have eq276 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq268 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq277 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq276 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq284 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq277 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq277 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq277 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq285 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq267
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq267 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq287 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq285
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq285
    | exact resolve eq285 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq388 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq284 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq284
    | exact resolve eq284 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq284 X1 (τ X0)
       grind)
    | exact superpose eq284 eq18
    | (have j1 := eq284 X1 (τ X0)
       grind)
    | exact resolve eq18 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq416 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq284 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1396 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq399 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq399
    | exact resolve eq399 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1414 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq399 X1 (τ X0)
       grind)
    | exact superpose eq399 eq17
    | (have j1 := eq399 X1 (τ X0)
       grind)
    | exact resolve eq17 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq399
  have eq1419 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1414 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1414
    | (have j0 := eq1414 X0 X1
       grind)
    | exact resolve eq1414 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414
  have eq1431 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1396 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1396
    | (have j0 := eq1396 X0 X1
       grind)
    | exact resolve eq1396 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396
  have eq1432 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1419 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1419
    | (have j0 := eq1419 X0 X1
       grind)
    | exact resolve eq1419 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419
  have eq1435 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1432 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1432
    | (have j0 := eq1432 X0 X1
       grind)
    | exact resolve eq1432 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1432
  have eq1491 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1435 X0 X1
       have i₂ := eq284 X0 X1
       grind)
    | exact superpose eq284 eq1435
    | (have j0 := eq1435 X1 X0
       have j1 := eq284 X1 X0
       grind)
    | exact resolve eq1435 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284 eq1435
  have eq1548 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1491 X0 X1
       have j1 := eq416 X1 X0
       grind)
    | (have r₁ := eq1491 X1 X0
       have r₂ := eq416 X0 X1
       grind)
    | exact resolve eq1491 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416 eq1491
  have eq1596 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (σ (M.op (τ X1) (τ (σ X0)))) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq1548 X1 (σ X0)
       grind)
    | exact superpose eq1548 eq28
    | (have j1 := eq1548 X1 (σ X0)
       grind)
    | exact resolve eq28 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1548
  have eq1612 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (σ (M.op (τ X1) (τ (σ X0)))) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1596 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1596
    | (have j0 := eq1596 X0 X1
       grind)
    | exact resolve eq1596 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596
  have eq1638 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (σ (M.op (τ X1) X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1612 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1612
    | (have j0 := eq1612 X0 X1
       grind)
    | exact resolve eq1612 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612
  have eq2315 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1638 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1638
    | exact resolve eq1638 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638
  have eq3902 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq287
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq287
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq287 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3903 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op y x) ∨ (M.op x y) = (k y x) := by grind
  clear eq3902
  have eq3904 : (M.op x y) = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq3903
       have r₂ := eq12 y x
       grind)
    | exact resolve eq3903 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3903
  have eq4097 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq388 y x
       have i₂ := eq3904
       grind)
    | exact superpose eq3904 eq388
    | (have j0 := eq388 y x
       grind)
    | exact resolve eq388 eq3904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388 eq3904
  have eq4106 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq4097
       have r₂ := eq287
       grind)
    | exact resolve eq4097 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287 eq4097
  have eq4108 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq4106
       have r₂ := eq16
       grind)
    | exact resolve eq4106 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4106
  have eq4110 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4108
       grind)
    | exact superpose eq4108 eq16
    | exact resolve eq16 eq4108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4108
  have eq4153 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4110
       have i₂ := eq2315 x y
       grind)
    | exact superpose eq2315 eq4110
    | (have j1 := eq2315 x y
       grind)
    | exact resolve eq4110 eq2315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2315
  have eq4158 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq4110
       have i₂ := eq1431 x y
       grind)
    | exact superpose eq1431 eq4110
    | (have j1 := eq1431 x y
       grind)
    | (have r₁ := eq4110
       have r₂ := eq1431 x y
       grind)
    | exact resolve eq4110 eq1431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1431 eq4110
  have eq4159 : y = (k y x) := by grind
  clear eq4158
  have eq4164 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have r₁ := eq4153
       have r₂ := eq16
       grind)
    | exact resolve eq4153 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4153
  have eq4171 : (σ y) ≠ (σ y) ∨ y = (M.op y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq4164
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq4164
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq4164 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4172 : y = (M.op y x) ∨ (M.op x y) = (k y x) := by grind
  clear eq4171
  have eq4173 : (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq4172
       have r₂ := eq12 y x
       grind)
    | exact resolve eq4172 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4172
  have eq4174 : y = (M.op x y) := by
    first
    | (have i₁ := eq4173
       have i₂ := eq4159
       grind)
    | exact superpose eq4159 eq4173
    | exact resolve eq4173 eq4159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4159 eq4173
  have eq4175 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq4164
       have i₂ := eq4174
       grind)
    | exact superpose eq4174 eq4164
    | exact resolve eq4164 eq4174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4164 eq4174
  have eq4198 : False := by grind
  exact eq4198

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_pyx_pyx_pxx_pyx_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq25 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq25 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
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
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
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
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq44 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq56 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq46 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq60 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq52
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       have j1 := eq59 X0 X1
       grind)
    | (have r₁ := eq60 X0 X1
       have r₂ := eq59 X0 X1
       grind)
    | exact resolve eq60 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq60
  have eq108 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq112 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq108 X0 X1
       have j1 := eq63 X1 X0
       grind)
    | (have r₁ := eq108 X1 X0
       have r₂ := eq63 X0 X1
       grind)
    | (have r₁ := eq108 X0 X0
       have r₂ := eq63 X0 X0
       grind)
    | exact resolve eq108 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq108
  have eq388 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq112 (σ X1) (σ X0)
       grind)
    | exact superpose eq112 eq15
    | exact resolve eq15 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq391 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq388 X0 X1
       have i₂ := eq112 X1 X0
       grind)
    | exact superpose eq112 eq388
    | exact resolve eq388 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq388
  have eq395 : False := by grind
  exact eq395

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyy_pxy_pyy_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq25 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq25 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
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
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
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
  have eq44 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq48 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X1 X1
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq46 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq47 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq47 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq47 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq61 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq53
    | (have j0 := eq53 X0 X1
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq53
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       have j1 := eq48 X1 X0
       grind)
    | (have r₁ := eq57 X1 X1
       have r₂ := eq48 X0 X1
       grind)
    | exact resolve eq57 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq57
  have eq144 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq63 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq149 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq144 X0 X1
       have j1 := eq61 X0 X1
       grind)
    | (have r₁ := eq144 X0 X1
       have r₂ := eq61 X0 X1
       grind)
    | (have r₁ := eq144 X0 X0
       have r₂ := eq61 X0 X0
       grind)
    | exact resolve eq144 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq144
  have eq240 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq149 (σ X0) (σ X1)
       grind)
    | exact superpose eq149 eq15
    | exact resolve eq15 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq240 X0 X1
       have i₂ := eq149 X0 X1
       grind)
    | exact superpose eq149 eq240
    | exact resolve eq240 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq240
  have eq246 : False := by grind
  exact eq246

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pxy_pxx_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq267 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq57 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57
    | exact resolve eq57 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq280 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq267 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq267
    | (have j0 := eq267 X0
       grind)
    | exact resolve eq267 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq267
  have eq283 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq280 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq280
    | (have j0 := eq280 X0
       grind)
    | exact resolve eq280 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq284 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq283 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq283 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq283 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq294 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq284 (σ X0)
       grind)
    | exact superpose eq284 eq15
    | exact resolve eq15 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq307 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq294 X0
       have i₂ := eq284 X0
       grind)
    | exact superpose eq284 eq294
    | exact resolve eq294 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284 eq294
  have eq359 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq16
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq1486 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq362 (τ X0) (τ X1)
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq362
    | (have j0 := eq362 (τ X0) (τ X1)
       grind)
    | exact resolve eq362 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1493 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1486 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1486
    | (have j0 := eq1486 X0 X1
       grind)
    | exact resolve eq1486 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1486
  have eq1496 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1493 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1493
    | (have j0 := eq1493 X0 X1
       grind)
    | exact resolve eq1493 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493
  have eq1498 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1496 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1496
    | (have j0 := eq1496 X0 X1
       grind)
    | exact resolve eq1496 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496
  have eq1499 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1498 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1498
    | (have j0 := eq1498 X0 X1
       grind)
    | exact resolve eq1498 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498
  have eq1500 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1499 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1499
    | (have j0 := eq1499 X0 X1
       grind)
    | exact resolve eq1499 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499
  have eq1501 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1500 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1500
    | (have j0 := eq1500 X0 X1
       grind)
    | exact resolve eq1500 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1500
  have eq2124 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq359
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq359
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq359
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq359
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq359 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq2125 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq2124
  have eq14433 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2125
       grind)
    | exact superpose eq2125 eq16
    | exact resolve eq16 eq2125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2125
  have eq14434 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq14433
       have r₂ := eq307 x
       grind)
    | exact resolve eq14433 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14433
  have eq14436 : y ≠ y ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq14434
       grind)
    | exact superpose eq14434 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq14434
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq14434
       grind)
    | exact resolve eq12 eq14434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14434
  have eq14454 : y = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14436
  have eq14460 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq362 x y
       have i₂ := eq14454
       grind)
    | exact superpose eq14454 eq362
    | (have j0 := eq362 x y
       grind)
    | exact resolve eq362 eq14454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq14454
  have eq14466 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14460
  have eq14467 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq14466
  have eq14670 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14467
       grind)
    | exact superpose eq14467 eq16
    | exact resolve eq16 eq14467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14672 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq14467
       grind)
    | exact superpose eq14467 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq14467
       grind)
    | exact resolve eq12 eq14467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14467
  have eq14690 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq14672
  have eq14693 : (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq14690
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq14690
    | exact resolve eq14690 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14690
  have eq14890 : y = (τ (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq14693
       grind)
    | exact superpose eq14693 eq10
    | exact resolve eq10 eq14693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14693
  have eq14961 : x = y ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq14890
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq14890
    | exact resolve eq14890 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14890
  have eq14972 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14961
       grind)
    | exact superpose eq14961 eq16
    | exact resolve eq16 eq14961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14961
  have eq14973 : (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq14972
       have r₂ := eq307 x
       grind)
    | exact resolve eq14972 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14972
  have eq15165 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq14973
       grind)
    | exact superpose eq14973 eq10
    | exact resolve eq10 eq14973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14973
  have eq15241 : y = (k x y) := by
    first
    | (have i₁ := eq15165
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq15165
    | exact resolve eq15165 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15165
  have eq15261 : y ≠ y ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1501 x y
       have i₂ := eq15241
       grind)
    | exact superpose eq15241 eq1501
    | (have j0 := eq1501 x y
       grind)
    | (have r₁ := eq1501 x y
       have r₂ := eq15241
       grind)
    | exact resolve eq1501 eq15241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501 eq15241
  have eq15264 : x = y ∨ y = (M.op x y) := by grind
  clear eq15261
  have eq15433 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15264
       grind)
    | exact superpose eq15264 eq16
    | exact resolve eq16 eq15264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15264
  have eq15438 : y = (M.op x y) := by
    first
    | (have r₁ := eq15433
       have r₂ := eq307 x
       grind)
    | exact resolve eq15433 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15433
  have eq15442 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14670
       have i₂ := eq15438
       grind)
    | exact superpose eq15438 eq14670
    | exact resolve eq14670 eq15438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14670 eq15438
  have eq15463 : (σ x) = (σ y) := by grind
  clear eq15442
  have eq15634 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq15463
       grind)
    | exact superpose eq15463 eq10
    | exact resolve eq10 eq15463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15463
  have eq15713 : x = y := by
    first
    | (have i₁ := eq15634
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15634
    | exact resolve eq15634 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15634
  have eq15728 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15713
       grind)
    | exact superpose eq15713 eq16
    | exact resolve eq16 eq15713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15713
  have eq15734 : False := by grind
  exact eq15734

/-- `Equation1488`: `x = (y ◇ x) ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation1488 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1488 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1488.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
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
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  clear eq49
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq72
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq72
    | exact resolve eq72 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq75
    | exact resolve eq75 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq76
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq76
    | exact resolve eq76 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq91 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq95 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq91
  have eq96 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq95
  have eq676 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 X1
       have i₂ := eq45 X1
       grind)
    | exact superpose eq45 eq69
    | (have j0 := eq69 X0 X1
       grind)
    | exact resolve eq69 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq69
  have eq741 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq676 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq10987 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq77 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10988 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq10987
    | exact resolve eq10987 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10987
  have eq10999 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq10988
       have r₂ := eq28
       grind)
    | exact resolve eq10988 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10988
  have eq11003 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq10999
    | exact resolve eq10999 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10999
  have eq11014 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (M.op (σ x) (σ y)) = (k X0 (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq11003 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq11003
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq11003
       grind)
    | exact resolve eq12 eq11003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11003
  have eq15683 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq11014
    | (have j0 := eq11014 (σ x)
       grind)
    | (have r₁ := eq11014 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq11014 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11014
  have eq15684 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq15683
  have eq15685 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq15684
  have eq15696 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq15685 eq77
    | exact resolve eq77 eq15685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq15685
  have eq15708 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq15696
  have eq15711 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq15708
       have r₂ := eq28
       grind)
    | exact resolve eq15708 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15708
  have eq15715 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq15711
       grind)
    | exact superpose eq15711 eq96
    | exact resolve eq96 eq15711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15724 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = X0 ∨ (M.op x y) = (k X0 y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq15711
       grind)
    | exact superpose eq15711 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq15711
       grind)
    | exact resolve eq12 eq15711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15711
  have eq15760 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq15715
    | exact resolve eq15715 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15715
  have eq22980 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15724 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15724
    | (have j0 := eq15724 x
       grind)
    | (have r₁ := eq15724 x
       have r₂ := eq19
       grind)
    | exact resolve eq15724 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15724
  have eq22981 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq22980
  have eq22982 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq22981
  have eq22999 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq741 x y
       have i₂ := eq22982
       grind)
    | exact superpose eq22982 eq741
    | (have j0 := eq741 x y
       grind)
    | exact resolve eq741 eq22982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741 eq22982
  have eq23003 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22999
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq22999
    | exact resolve eq22999 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22999
  have eq23015 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq23003
    | exact resolve eq23003 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23003
  have eq23020 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq23015
       have r₂ := eq15760
       grind)
    | exact resolve eq23015 eq15760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23015
  have eq23023 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23020
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq23020
    | exact resolve eq23020 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq23020
  have eq23026 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23023
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq23023
    | exact resolve eq23023 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23023
  have eq23029 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23026
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq23026
    | exact resolve eq23026 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23026
  have eq23032 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq23029
    | exact resolve eq23029 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23029
  have eq23035 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23032
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq23032
    | exact resolve eq23032 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23032
  have eq23038 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23035
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq23035
    | exact resolve eq23035 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23035
  have eq23039 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq23038
  have eq23110 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq23039 eq15760
    | exact resolve eq15760 eq23039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15760 eq23039
  have eq23173 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq23110
  have eq23181 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq23173
       have r₂ := eq28
       grind)
    | exact resolve eq23173 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23173
  have eq23184 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq23181 eq30
    | exact resolve eq30 eq23181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq23181
  have eq23303 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq23184
    | exact resolve eq23184 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq23184
  have eq23304 : x = y := by grind
  clear eq23303
  have eq23323 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq23304
       grind)
    | exact superpose eq23304 eq19
    | exact resolve eq19 eq23304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq23324 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq23304
       grind)
    | exact superpose eq23304 eq25
    | exact resolve eq25 eq23304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq23304
  have eq23448 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq23324
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq23324
    | exact resolve eq23324 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq23324
  have eq23467 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23448 eq27
    | exact resolve eq27 eq23448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq23448
  have eq23691 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq23467 eq68
    | exact resolve eq68 eq23467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq23467
  have eq23726 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq23691
       have i₂ := eq23323
       grind)
    | exact superpose eq23323 eq23691
    | exact resolve eq23691 eq23323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23323 eq23691
  have eq23743 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23726 eq15
    | exact resolve eq15 eq23726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23726
  have eq23820 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq23743
    | exact resolve eq23743 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23743
  have eq23841 : False := by grind
  exact eq23841
