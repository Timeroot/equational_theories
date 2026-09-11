import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_x_y_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq79 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq69
       grind)
    | exact superpose eq69 eq16
    | exact resolve eq16 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq69
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq69 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
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
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq110
    | exact resolve eq110 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq330 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq446 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3 X4
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq61
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq455 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq60 eq61
    | exact resolve eq61 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq61
    | (have j0 := eq61 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq61 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq466 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq14
    | exact resolve eq14 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq466 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq466
    | exact resolve eq466 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq470 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq457
    | (have j0 := eq457 X0 X1
       grind)
    | exact resolve eq457 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq472 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq455 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq455
    | exact resolve eq455 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq478 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq469 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq469
    | (have j0 := eq469 x y
       grind)
    | exact resolve eq469 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq701 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq90 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq702 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq701 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq3086 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq470 eq61
    | exact resolve eq61 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3101 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3086 eq470
    | exact resolve eq470 eq3086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470 eq3086
  have eq3119 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq3101 eq14
    | exact resolve eq14 eq3101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3101
  have eq3121 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq3119 X0
       have i₂ := eq469 (M.op sF4 sF4) (M.op (M.op sF4 sF4) X0)
       grind)
    | (have i₁ := eq3119 x
       have i₂ := eq469 (M.op sF4 sF4) x
       grind)
    | exact superpose eq469 eq3119
    | exact resolve eq3119 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3119
  have eq3357 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 X0 x X0
       have i₂ := eq472 X0 X0 x
       grind)
    | exact superpose eq472 eq61
    | exact resolve eq61 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq3393 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq472 X0 X0 X0
       have i₂ := eq3357 X0
       grind)
    | exact superpose eq3357 eq472
    | exact resolve eq472 eq3357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3357
  have eq3433 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq702 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq702
    | (have j0 := eq702 (τ X0)
       grind)
    | exact resolve eq702 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq3444 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3433 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3433
    | (have j0 := eq3433 X0
       grind)
    | exact resolve eq3433 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3433
  have eq3451 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3444 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3444
    | (have j0 := eq3444 X0
       grind)
    | exact resolve eq3444 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3444
  have eq3814 : ∀ X0 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X2)) X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq446 X0 X0 x X0 X2
       have i₂ := eq472 X0 X0 x
       grind)
    | exact superpose eq472 eq446
    | exact resolve eq446 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq4933 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq3393 X0
       grind)
    | exact superpose eq3393 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq3393 X0
       grind)
    | exact resolve eq13 eq3393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4943 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4933 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4933
  have eq4982 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq330 X0 (M.op X1 X1)
       have i₂ := eq4943 X1 (σ X0)
       grind)
    | exact superpose eq4943 eq330
    | exact resolve eq330 eq4943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq4988 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4982 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq4982
    | exact resolve eq4982 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4982
  have eq25787 : (σ x) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq3121 eq464
    | exact resolve eq464 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq25788 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq3121 eq14
    | exact resolve eq14 eq3121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3121
  have eq25843 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25788 X0
       have i₂ := eq3393 sF4
       grind)
    | exact superpose eq3393 eq25788
    | exact resolve eq25788 eq3393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3393 eq25788
  have eq25844 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq25787
       have i₂ := eq3814 sF4 sF4
       grind)
    | exact superpose eq3814 eq25787
    | exact resolve eq25787 eq3814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3814 eq25787
  have eq26209 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq25844 eq60
    | exact resolve eq60 eq25844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq25844
  have eq26314 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) X1) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) := by
    intro X0 X1
    first
    | exact superpose eq25843 eq472
    | exact resolve eq472 eq25843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq26341 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq25843 eq26314
    | exact resolve eq26314 eq25843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25843 eq26314
  have eq27380 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 X0
       have i₂ := eq26341 X0 X1
       grind)
    | exact superpose eq26341 eq14
    | exact resolve eq14 eq26341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28344 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq111 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq28345 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq28344
    | exact resolve eq28344 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28344
  have eq28356 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq28345
       have r₂ := eq27
       grind)
    | exact resolve eq28345 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28345
  have eq28363 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28356 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq28356
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq28356
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq28356
       grind)
    | exact resolve eq12 eq28356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28356
  have eq28392 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq28363
  have eq28393 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq28392
  have eq28499 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28393 eq79
    | exact resolve eq79 eq28393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq28393
  have eq28529 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq28499
    | exact resolve eq28499 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28499
  have eq28533 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq28529
       have r₂ := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq28529
       have r₂ := eq12 y x
       grind)
    | (have r₁ := eq28529
       have r₂ := eq12 x x
       grind)
    | exact resolve eq28529 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28529
  have eq28547 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (k y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq28533 eq4988
    | exact resolve eq4988 eq28533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4988 eq28533
  have eq28594 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (k y x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq28 eq28547
    | exact resolve eq28547 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq28547
  have eq28601 : ∀ X0 : G, x = (k y x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq28594 X0
       have j1 := eq13 X0 x
       grind)
    | (have r₁ := eq28594 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq28594 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28594
  have eq28617 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 y x
       have i₂ := eq28601 X0
       grind)
    | exact superpose eq28601 eq11
    | (have j0 := eq11 y x
       have j1 := eq28601 X0
       grind)
    | exact resolve eq11 eq28601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28601
  have eq28620 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op y x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq28617 X0
       have j1 := eq13 X0 x
       grind)
    | (have r₁ := eq28617 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq28617 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28617
  have eq28636 : ∀ X0 : G, y = (M.op y x) ∨ x = (M.op x y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq28620 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28620
    | (have j0 := eq28620 X0
       grind)
    | exact resolve eq28620 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28620
  have eq29098 : ∀ X0 : G, y = (M.op y y) ∨ x = (M.op x y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq469 y x
       have i₂ := eq28636 X0
       grind)
    | exact superpose eq28636 eq469
    | (have j1 := eq28636 X0
       grind)
    | exact resolve eq469 eq28636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469 eq28636
  have eq29661 : ∀ X0 X1 : G, (k X1 x) = X1 ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4943 y X0
       have i₂ := eq29098 X1
       grind)
    | exact superpose eq29098 eq4943
    | (have j1 := eq29098 X1
       grind)
    | exact resolve eq4943 eq29098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29672 : ∀ X0 X1 : G, (k X1 x) = X1 ∨ x = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27380 y X0
       have i₂ := eq29098 X1
       grind)
    | exact superpose eq29098 eq27380
    | (have j1 := eq29098 X1
       grind)
    | exact resolve eq27380 eq29098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29098
  have eq30668 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq702 x
       have i₂ := eq29661 X0 x
       grind)
    | exact superpose eq29661 eq702
    | (have j0 := eq702 x
       have j1 := eq29661 X0 x
       grind)
    | exact resolve eq702 eq29661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29661
  have eq30699 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq30668 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30668
  have eq30728 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq30699 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30699
    | (have j0 := eq30699 X0
       grind)
    | exact resolve eq30699 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30699
  have eq30852 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3451 x
       have i₂ := eq29672 X0 x
       grind)
    | exact superpose eq29672 eq3451
    | (have j0 := eq3451 x
       have j1 := eq29672 X0 x
       grind)
    | (have r₁ := eq3451 x
       have r₂ := eq29672 X0 x
       grind)
    | exact resolve eq3451 eq29672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3451 eq29672
  have eq30885 : ∀ X0 : G, x = (M.op x x) ∨ x = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq30852 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30852
  have eq32102 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq26209
       have i₂ := eq30728 (M.op sF2 sF2)
       grind)
    | exact superpose eq30728 eq26209
    | (have j1 := eq30728 X0
       grind)
    | exact resolve eq26209 eq30728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26209 eq30728
  have eq32160 : ∀ X0 : G, (k X0 y) = X0 ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq32102
    | (have j0 := eq32102 X0
       grind)
    | exact resolve eq32102 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32102
  have eq32218 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq702 y
       have i₂ := eq32160 y
       grind)
    | exact superpose eq32160 eq702
    | (have j0 := eq702 y
       grind)
    | exact resolve eq702 eq32160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32160
  have eq32249 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32218
  have eq32278 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32249
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32249
    | exact resolve eq32249 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32249
  have eq32895 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq32278 eq27380
    | exact resolve eq27380 eq32278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32278
  have eq33335 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq32895 eq26341
    | exact resolve eq26341 eq32895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32895
  have eq33650 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33335 eq26
    | (have j1 := eq33335 (σ x)
       grind)
    | exact resolve eq26 eq33335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33335
  have eq33673 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq33650
  have eq33694 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33673 eq27
    | exact resolve eq27 eq33673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33673
  have eq50826 : ∀ X0 X1 : G, (M.op y X1) = X1 ∨ x = (M.op x y) ∨ (M.op x X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27380 x X0
       have i₂ := eq30885 X1
       grind)
    | exact superpose eq30885 eq27380
    | (have j1 := eq30885 X1
       grind)
    | exact resolve eq27380 eq30885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30885
  have eq89113 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26341 y X0
       have i₂ := eq50826 X1 X0
       grind)
    | exact superpose eq50826 eq26341
    | (have j1 := eq50826 X1 X1
       grind)
    | exact resolve eq26341 eq50826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26341 eq50826
  have eq93811 : y ≠ y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq89113 x y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89113
  have eq93812 : x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq93811
  have eq93822 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq93812
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93812
    | exact resolve eq93812 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93812
  have eq93845 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq93822 eq20
    | exact resolve eq20 eq93822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93822
  have eq94139 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq93845
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq93845
    | exact resolve eq93845 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93845
  have eq94140 : x = (M.op x y) := by
    first
    | (have r₁ := eq94139
       have r₂ := eq33694
       grind)
    | exact resolve eq94139 eq33694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33694 eq94139
  have eq94457 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq94140 eq20
    | exact resolve eq20 eq94140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq94525 : x = (M.op x x) := by
    first
    | exact superpose eq94140 eq478
    | exact resolve eq478 eq94140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq94757 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq94457
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq94457
    | exact resolve eq94457 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94457
  have eq94761 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq94757 eq26
    | exact resolve eq26 eq94757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq94974 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq4943 x X0
       have i₂ := eq94525
       grind)
    | exact superpose eq94525 eq4943
    | exact resolve eq4943 eq94525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4943
  have eq94985 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq27380 x X0
       have i₂ := eq94525
       grind)
    | exact superpose eq94525 eq27380
    | exact resolve eq27380 eq94525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94525
  have eq96270 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq702 x
       have i₂ := eq94974 x
       grind)
    | exact superpose eq94974 eq702
    | (have j0 := eq702 x
       grind)
    | exact resolve eq702 eq94974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq94974
  have eq96355 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq96270
  have eq96439 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq96355
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq96355
    | exact resolve eq96355 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96355
  have eq96588 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq94757 eq96439
    | exact resolve eq96439 eq94757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96439
  have eq96905 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq94985 y
       grind)
    | exact superpose eq94985 eq18
    | (have j1 := eq94985 y
       grind)
    | exact resolve eq18 eq94985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq94985
  have eq97045 : x = y := by
    first
    | exact superpose eq94140 eq96905
    | exact resolve eq96905 eq94140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94140 eq96905
  have eq97117 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq97045
       grind)
    | exact superpose eq97045 eq24
    | exact resolve eq24 eq97045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq97045
  have eq97402 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq97117
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq97117
    | exact resolve eq97117 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq97117
  have eq97520 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq94757 eq97402
    | exact resolve eq97402 eq94757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94757 eq97402
  have eq99497 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq96588 eq27380
    | exact resolve eq27380 eq96588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27380 eq96588
  have eq99891 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq99497 eq94761
    | exact resolve eq94761 eq99497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94761 eq99497
  have eq100025 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq97520 eq99891
    | exact resolve eq99891 eq97520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97520 eq99891
  have eq100051 : False := by grind
  exact eq100051

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_x_pyy_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
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
  clear eq18
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq69 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq69
    | exact resolve eq69 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq72 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq66 X0 x x X3 X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq66
    | exact resolve eq66 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq177 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 X0 x X0
       have i₂ := eq72 X0 X0 x
       grind)
    | exact superpose eq72 eq61
    | exact resolve eq61 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq188 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq72 X0 X0 X0
       have i₂ := eq177 X0
       grind)
    | exact superpose eq177 eq72
    | exact resolve eq72 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq177
  have eq201 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq188 X0
       grind)
    | exact superpose eq188 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq188 X0
       grind)
    | exact resolve eq12 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op X0 X0) X1
       have i₂ := eq188 X0
       grind)
    | exact superpose eq188 eq9
    | exact resolve eq9 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq201 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq208 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq206 X0 X1
       have i₂ := eq71 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq206 X0 X1
       have i₂ := eq71 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq71 eq206
    | exact resolve eq206 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq206
  have eq216 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op X1 X1)
       have i₂ := eq207 X1 (σ X0)
       grind)
    | exact superpose eq207 eq28
    | exact resolve eq28 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 X1)
       have i₂ := eq207 X1 (τ X0)
       grind)
    | exact superpose eq207 eq17
    | exact resolve eq17 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq224 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq219 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq219
    | exact resolve eq219 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq227 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq216 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq216
    | exact resolve eq216 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq470 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq208 X0 X1
       grind)
    | exact superpose eq208 eq9
    | exact resolve eq9 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq477 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq470 X0 X1
       have i₂ := eq188 X0
       grind)
    | exact superpose eq188 eq470
    | exact resolve eq470 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq470
  have eq603 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq619 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq224 (σ (M.op X0 X0)) X0
       have i₂ := eq603 (σ (M.op X0 X0))
       grind)
    | exact superpose eq603 eq224
    | (have j1 := eq603 (σ (M.op X0 X0))
       grind)
    | exact resolve eq224 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq639 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq603 (τ X0)
       grind)
    | exact superpose eq603 eq17
    | (have j1 := eq603 (τ X0)
       grind)
    | exact resolve eq17 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq603
  have eq651 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq619 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq666 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq639 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq639
    | (have j0 := eq639 X0
       grind)
    | exact resolve eq639 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq730 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq1129 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) X2) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k X2 (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq730 X0 X0
       grind)
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq730 X0 X1
       grind)
    | exact superpose eq730 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq730 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq730 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq730 X0 X0
       grind)
    | exact resolve eq13 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1159 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq730 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq1164 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) X2) ∨ (M.op (σ X0) (σ X1)) = (k X2 (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1129 X0 X1 X2
       have j1 := eq1159 X0 X1
       grind)
    | (have r₁ := eq1129 X0 X1 X2
       have r₂ := eq1159 X0 X1
       grind)
    | (have r₁ := eq1129 X1 X1 X2
       have r₂ := eq1159 X1 X1
       grind)
    | exact resolve eq1129 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129 eq1159
  have eq1412 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq477 (σ (M.op X0 X0)) X1
       have i₂ := eq651 X0
       grind)
    | exact superpose eq651 eq477
    | exact resolve eq477 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq2064 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq666 X0
       grind)
    | exact superpose eq666 eq10
    | (have j1 := eq666 X0
       grind)
    | exact resolve eq10 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq23360 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1164 X0 X1 (σ X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164
  have eq23363 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23360 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq23360
    | (have j0 := eq23360 X0 X1
       grind)
    | exact resolve eq23360 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23360
  have eq23364 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq23363 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23363
  have eq23399 : ∀ X1 X2 : G, (M.op (σ X1) (σ X2)) = (σ (k X2 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X1 X2
    first
    | (have j0 := eq23364 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23364
  have eq23419 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq23399 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23399
  have eq23435 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq23419 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23419
  have eq23438 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq23435 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23435
  have eq23440 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq23438 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23438
  have eq24326 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23440 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq23440
    | (have j0 := eq23440 (τ X1) X1
       grind)
    | exact resolve eq23440 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq24420 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24326 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24326
    | (have j0 := eq24326 X0 X1
       grind)
    | exact resolve eq24326 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24326
  have eq24476 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24420 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq24420
    | (have j0 := eq24420 X0 X1
       grind)
    | exact resolve eq24420 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24420
  have eq24491 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24476 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq24476
    | (have j0 := eq24476 X0 X1
       grind)
    | exact resolve eq24476 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24476
  have eq24496 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24491 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24491
    | (have j0 := eq24491 X0 X1
       grind)
    | exact resolve eq24491 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24491
  have eq24646 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23440 X0 X1
       have i₂ := eq24496 X1 X0
       grind)
    | exact superpose eq24496 eq23440
    | (have j0 := eq23440 X0 X1
       have j1 := eq24496 X0 (σ X0)
       grind)
    | exact resolve eq23440 eq24496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23440 eq24496
  have eq39937 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq2064 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2064
  have eq53633 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq39937 (σ X0)
       have i₂ := eq28 X0 (σ X0)
       grind)
    | exact superpose eq28 eq39937
    | (have j0 := eq39937 (σ X0)
       grind)
    | exact resolve eq39937 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq39937
  have eq53705 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq53633 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq53633
    | (have j0 := eq53633 X0
       grind)
    | exact resolve eq53633 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53633
  have eq53738 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53705 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq53705
    | (have j0 := eq53705 X0
       grind)
    | exact resolve eq53705 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53705
  have eq515599 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq24646 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24646
  have eq515727 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq515599 x y
       grind)
    | exact superpose eq515599 eq16
    | (have j1 := eq515599 x x
       grind)
    | (have r₁ := eq16
       have r₂ := eq515599 x y
       grind)
    | exact resolve eq16 eq515599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515599
  have eq516140 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq515727
  have eq516516 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq227 X0 (σ x)
       have i₂ := eq516140
       grind)
    | exact superpose eq516140 eq227
    | exact resolve eq227 eq516140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq516140
  have eq516934 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq516516 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq516516
    | exact resolve eq516516 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516516
  have eq516965 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq516934 X0
       have j1 := eq12 X0 x
       grind)
    | (have r₁ := eq516934 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq516934 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516934
  have eq517195 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq53738 x
       have i₂ := eq516965 x
       grind)
    | exact superpose eq516965 eq53738
    | (have j0 := eq53738 x
       grind)
    | (have r₁ := eq53738 x
       have r₂ := eq516965 x
       grind)
    | exact resolve eq53738 eq516965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53738 eq516965
  have eq517526 : x = (M.op x x) := by grind
  clear eq517195
  have eq517653 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq477 x X0
       have i₂ := eq517526
       grind)
    | exact superpose eq517526 eq477
    | exact resolve eq477 eq517526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq517668 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1412 x X0
       have i₂ := eq517526
       grind)
    | exact superpose eq517526 eq1412
    | exact resolve eq1412 eq517526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412 eq517526
  have eq518048 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq517653 y
       grind)
    | exact superpose eq517653 eq16
    | exact resolve eq16 eq517653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517653
  have eq530013 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq518048
       have i₂ := eq517668 (σ y)
       grind)
    | exact superpose eq517668 eq518048
    | (have r₁ := eq518048
       have r₂ := eq517668 (σ y)
       grind)
    | exact resolve eq518048 eq517668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517668 eq518048
  have eq530418 : False := by grind
  exact eq530418

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pxx_y_pxy_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
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
  have eq69 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq70 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq72 : y ≠ (M.op x y) ∨ x = (M.op x x) ∨ x = (k y x) := by
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
  have eq74 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 (M.op (M.op X1 X0) X2)) = (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X1 (M.op (M.op X1 X0) X2))) ∨ (M.op X1 (M.op (M.op X1 X0) X2)) = (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 X0) X2)) = (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X1 (M.op (M.op X1 X0) X2))) ∨ (M.op X1 (M.op (M.op X1 X0) X2)) = (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq74 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq80 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq69
       grind)
    | exact superpose eq69 eq16
    | exact resolve eq16 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq93 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq69
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq69 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
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
  clear eq44
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99
    | exact resolve eq99 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq111 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq110
    | exact resolve eq110 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq168 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq182 : (σ (k (k y y) y)) = (k (k (σ y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq40 (k y y)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq40
    | exact resolve eq40 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq214 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ y) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq34
  have eq451 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3 X4
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq460 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X1)) (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq462 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq471 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq475 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq471 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq471
    | exact resolve eq471 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq476 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq462
    | (have j0 := eq462 X0 X1
       grind)
    | exact resolve eq462 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq477 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X1)) (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq461 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq461
    | (have j0 := eq461 X0 X1
       grind)
    | exact resolve eq461 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq478 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq460 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq460
    | exact resolve eq460 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq609 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq91 X0 X0
       grind)
    | exact superpose eq91 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq91 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq91 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq614 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq609 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq615 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq614 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq614 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq614 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq759 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0)) ∨ (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = (k (M.op X0 X3) (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq75 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq75
    | exact resolve eq75 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq785 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = (k (M.op X0 X3) (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq759 X0 X1 X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq759
    | (have j0 := eq759 X0 X1 X2 X3
       grind)
    | exact resolve eq759 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq791 : ∀ X0 X3 : G, (k (M.op X0 X3) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq785 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq785
    | (have j0 := eq785 X0 x x X3
       grind)
    | exact resolve eq785 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq3167 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq476 eq52
    | exact resolve eq52 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3185 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3167 eq476
    | exact resolve eq476 eq3167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476 eq3167
  have eq3214 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X1)) (M.op (M.op (M.op x y) X0) X2)) (M.op (M.op (M.op x y) X0) X3)) (M.op (M.op x y) X0)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq477 eq52
    | exact resolve eq52 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq3284 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 X0 x X0
       have i₂ := eq478 X0 X0 x
       grind)
    | exact superpose eq478 eq52
    | exact resolve eq52 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq3322 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq478 X0 X0 X0
       have i₂ := eq3284 X0
       grind)
    | exact superpose eq3284 eq478
    | exact resolve eq478 eq3284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3335 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq791 (M.op X0 X0) X0
       have i₂ := eq3284 X0
       grind)
    | exact superpose eq3284 eq791
    | (have j0 := eq791 (M.op X0 X0) x
       grind)
    | exact resolve eq791 eq3284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3340 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq3335 X0
       have j1 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq3335 X0
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | exact resolve eq3335 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3335
  have eq3480 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (k X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq3185 eq13
    | (have j0 := eq13 X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       have r₂ := eq3185
       grind)
    | exact resolve eq13 eq3185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3487 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq3480 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3480
  have eq3547 : ∀ X0 : G, (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ≠ (σ (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op X0 X0) = (k X0 (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq3487 eq615
    | (have j0 := eq615 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0
       grind)
    | exact resolve eq615 eq3487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3564 : ∀ X0 : G, (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ≠ (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op X0 X0) = (k X0 (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq3185 eq3547
    | (have j0 := eq3547 X0
       grind)
    | exact resolve eq3547 eq3185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3185 eq3547
  have eq3565 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have j0 := eq3564 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3564
  have eq3630 : (M.op (σ x) (σ x)) = (σ (k x (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq3565 eq35
    | exact resolve eq35 eq3565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq3631 : (M.op (σ y) (σ y)) = (σ (k y (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq3565 eq36
    | exact resolve eq36 eq3565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq3565
  have eq3654 : (σ (M.op y y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3487 eq3631
    | exact resolve eq3631 eq3487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3631
  have eq3655 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq3487 eq3630
    | exact resolve eq3630 eq3487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3487 eq3630
  have eq3766 : ∀ X0 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X2)) X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq451 X0 X0 x X0 X2
       have i₂ := eq478 X0 X0 x
       grind)
    | exact superpose eq478 eq451
    | exact resolve eq451 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq3859 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq3654
       grind)
    | exact superpose eq3654 eq16
    | exact resolve eq16 eq3654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3882 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq3655
       grind)
    | exact superpose eq3655 eq16
    | exact resolve eq16 eq3655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4010 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq168 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq168
    | (have j0 := eq168 x
       grind)
    | exact resolve eq168 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq4025 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4010
  have eq4031 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4025
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq4025
    | exact resolve eq4025 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq4025
  have eq4047 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq4031
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq4031 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4031
  have eq4053 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq4047 eq49
    | exact resolve eq49 eq4047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq4047
  have eq4121 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq4053 eq3882
    | exact resolve eq3882 eq4053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3882
  have eq4262 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq190 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq190
    | (have j0 := eq190 y
       grind)
    | exact resolve eq190 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq4275 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq4262
  have eq4280 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4275
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq4275
    | exact resolve eq4275 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq4275
  have eq4303 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq4280
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq4280 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4280
  have eq4327 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq4303 eq85
    | exact resolve eq85 eq4303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq4331 : (k y y) = (M.op y y) := by
    first
    | exact superpose eq3859 eq4327
    | exact resolve eq4327 eq3859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4327
  have eq4337 : (k (k (σ y) (σ y)) (σ y)) = (σ (k (M.op y y) y)) := by
    first
    | (have i₁ := eq182
       have i₂ := eq4331
       grind)
    | exact superpose eq4331 eq182
    | exact resolve eq182 eq4331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq4331
  have eq4345 : (σ (k (M.op y y) y)) = (k (M.op (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq4303 eq4337
    | exact resolve eq4337 eq4303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4303 eq4337
  have eq5035 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq3322 X0
       grind)
    | exact superpose eq3322 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq3322 X0
       grind)
    | exact resolve eq13 eq3322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5053 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq5035 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5035
  have eq5091 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (k X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5053 X0 X2
       have i₂ := eq5053 X1 X0
       grind)
    | exact superpose eq5053 eq5053
    | exact resolve eq5053 eq5053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5143 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq615 (M.op X0 X0) X1
       have i₂ := eq5053 X0 (M.op X0 X0)
       grind)
    | exact superpose eq5053 eq615
    | (have j0 := eq615 (M.op X0 X0) X1
       grind)
    | exact resolve eq615 eq5053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615 eq5053
  have eq5165 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5143 X0 X1
       have i₂ := eq3322 X0
       grind)
    | exact superpose eq3322 eq5143
    | (have j0 := eq5143 X0 X1
       grind)
    | exact resolve eq5143 eq3322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5143
  have eq5166 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq5165 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5165
  have eq5616 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq233 X0 (M.op X1 X1)
       have i₂ := eq5166 X1 X0
       grind)
    | exact superpose eq5166 eq233
    | exact resolve eq233 eq5166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233 eq5166
  have eq5824 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1)) (σ (k y X0))) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | exact superpose eq93 eq214
    | (have j1 := eq93 X0
       grind)
    | exact resolve eq214 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq214
  have eq7765 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5616 X0 (τ X0)
       have i₂ := eq3340 (τ X0)
       grind)
    | exact superpose eq3340 eq5616
    | exact resolve eq5616 eq3340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3340
  have eq7804 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5091 (τ X0) x X1
       have i₂ := eq5616 X0 x
       grind)
    | exact superpose eq5616 eq5091
    | exact resolve eq5091 eq5616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5091 eq5616
  have eq7924 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq7765 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq7765
    | exact resolve eq7765 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7765
  have eq8760 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 (M.op (σ X0) (σ X0))
       have i₂ := eq7924 X0
       grind)
    | exact superpose eq7924 eq15
    | exact resolve eq15 eq7924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7924
  have eq54452 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq112 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq54453 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq54452
    | exact resolve eq54452 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54452
  have eq54465 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq54453
       have r₂ := eq27
       grind)
    | exact resolve eq54453 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54453
  have eq54517 : ∀ X0 : G, (M.op X0 X0) = (k X0 (τ (σ y))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq54465 eq7804
    | exact resolve eq7804 eq54465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7804 eq54465
  have eq54624 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq29 eq54517
    | exact resolve eq54517 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54517
  have eq54663 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq54624 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq54624 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq54624 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54624
  have eq54745 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq54663 (M.op X0 X0)
       have i₂ := eq3322 X0
       grind)
    | exact superpose eq3322 eq54663
    | exact resolve eq54663 eq3322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54663
  have eq60633 : (σ (M.op y y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq4345
       have i₂ := eq54745 y
       grind)
    | exact superpose eq54745 eq4345
    | exact resolve eq4345 eq54745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4345 eq54745
  have eq60661 : (M.op (σ y) (σ y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq60633
       have i₂ := eq3654
       grind)
    | exact superpose eq3654 eq60633
    | exact resolve eq60633 eq3654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3654 eq60633
  have eq73014 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq60661 eq791
    | (have j0 := eq791 (σ y) x
       grind)
    | exact resolve eq791 eq60661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60661
  have eq73021 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq73014
  have eq73134 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq73021 eq478
    | exact resolve eq478 eq73021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73172 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq73134 X0
       have i₂ := eq475 sF3 (M.op sF3 X0)
       grind)
    | (have i₁ := eq73134 x
       have i₂ := eq475 sF3 x
       grind)
    | exact superpose eq475 eq73134
    | exact resolve eq73134 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73134
  have eq74496 : ∀ X0 : G, (M.op (M.op (σ y) (σ y)) X0) = X0 ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq73172 eq14
    | exact resolve eq14 eq73172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73172
  have eq76394 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq73021 eq74496
    | exact resolve eq74496 eq73021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73021 eq74496
  have eq76586 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) X0) = X0 ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq76394 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76394
  have eq76655 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have j0 := eq76586 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76586
  have eq76656 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq76655
  have eq77253 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq76656 eq791
    | (have j0 := eq791 (σ y) x
       grind)
    | exact resolve eq791 eq76656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791 eq76656
  have eq79248 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq77253 eq57
    | exact resolve eq57 eq77253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq77253
  have eq79302 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq79248
    | exact resolve eq79248 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79248
  have eq79803 : (τ (σ y)) = (M.op y y) ∨ y = (k x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq79302 eq3859
    | exact resolve eq3859 eq79302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3859 eq79302
  have eq79999 : y = (M.op y y) ∨ y = (k x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq79803
    | exact resolve eq79803 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq79803
  have eq80023 : y = (k x y) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq79999
       have r₂ := eq12 y y
       grind)
    | (have r₁ := eq79999
       have r₂ := eq12 x y
       grind)
    | exact resolve eq79999 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79999
  have eq80555 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq80023
       grind)
    | exact superpose eq80023 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq80023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80023
  have eq80556 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op y y) := by grind
  clear eq80555
  have eq80560 : y = (M.op y y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq80556
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq80556
    | exact resolve eq80556 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80556
  have eq81249 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq478 y y x
       have i₂ := eq80560
       grind)
    | exact superpose eq80560 eq478
    | exact resolve eq478 eq80560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81285 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq81249 X0
       have i₂ := eq475 y X0
       grind)
    | (have i₁ := eq81249 X0
       have i₂ := eq475 y (M.op y X0)
       grind)
    | exact superpose eq475 eq81249
    | exact resolve eq81249 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81249
  have eq90791 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq81285 X0
       grind)
    | exact superpose eq81285 eq14
    | exact resolve eq14 eq81285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81285
  have eq100906 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq90791 X0
       have i₂ := eq80560
       grind)
    | exact superpose eq80560 eq90791
    | exact resolve eq90791 eq80560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80560 eq90791
  have eq101110 : ∀ X0 : G, x = (M.op y x) ∨ (M.op y X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq100906 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100906
  have eq101178 : x ≠ x ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq101110 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101110
  have eq101179 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq101178
  have eq101186 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq111
       have i₂ := eq101179
       grind)
    | exact superpose eq101179 eq111
    | exact resolve eq111 eq101179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq101220 : y = (M.op (M.op (M.op y y) x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3766 y x
       have i₂ := eq101179
       grind)
    | exact superpose eq101179 eq3766
    | exact resolve eq3766 eq101179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3766 eq101179
  have eq101233 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq101186
  have eq101236 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq101233
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq101233
    | exact resolve eq101233 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101233
  have eq102343 : (M.op (M.op y y) x) = (M.op (M.op (M.op y y) y) (M.op (M.op y y) x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq478 (M.op y y) x y
       have i₂ := eq101220
       grind)
    | exact superpose eq101220 eq478
    | exact resolve eq478 eq101220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102404 : (M.op (M.op y y) x) = (M.op y (M.op (M.op y y) x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq102343
       have i₂ := eq3284 y
       grind)
    | exact superpose eq3284 eq102343
    | exact resolve eq102343 eq3284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3284 eq102343
  have eq103015 : (τ (σ x)) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq101236 eq80
    | exact resolve eq80 eq101236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq101236
  have eq103042 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq103015
    | exact resolve eq103015 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103015
  have eq103048 : x = (k y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq103042
       have r₂ := eq72
       grind)
    | exact resolve eq103042 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq103042
  have eq322207 : (M.op y y) = (M.op (M.op (M.op y y) x) (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq478 y y x
       have i₂ := eq102404
       grind)
    | exact superpose eq102404 eq478
    | exact resolve eq478 eq102404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102404
  have eq341844 : x = (M.op (M.op (M.op y y) (M.op y y)) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14 x (M.op y y) (M.op y y)
       have i₂ := eq322207
       grind)
    | exact superpose eq322207 eq14
    | exact resolve eq14 eq322207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322207
  have eq341937 : x = (M.op (M.op y y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq341844
       have i₂ := eq3322 y
       grind)
    | exact superpose eq3322 eq341844
    | exact resolve eq341844 eq3322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341844
  have eq343349 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq101220
       have i₂ := eq341937
       grind)
    | exact superpose eq341937 eq101220
    | exact resolve eq101220 eq341937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101220 eq341937
  have eq343449 : y = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq343349
  have eq343462 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq343449
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq343449
    | exact resolve eq343449 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq343449
  have eq343463 : y = (M.op x y) := by grind
  clear eq343462
  have eq343466 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq343463 eq20
    | exact resolve eq20 eq343463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq343887 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq343466
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq343466
    | exact resolve eq343466 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq343466
  have eq343950 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq343887 eq26
    | exact resolve eq26 eq343887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq362161 : ∀ X0 X1 X2 X3 : G, (M.op y X0) = (M.op (M.op (M.op (M.op y (M.op (M.op y X0) X1)) (M.op (M.op y X0) X2)) (M.op (M.op y X0) X3)) (M.op y X0)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq343463 eq3214
    | exact resolve eq3214 eq343463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3214 eq343463
  have eq362243 : ∀ X0 X1 : G, (M.op y y) = (M.op (M.op (M.op (M.op y (M.op (M.op y y) X0)) (M.op y y)) (M.op (M.op y y) X1)) (M.op y y)) := by
    intro X0 X1
    first
    | (have i₁ := eq362161 y X0 (M.op y y) X1
       have i₂ := eq3322 y
       grind)
    | exact superpose eq3322 eq362161
    | exact resolve eq362161 eq3322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362161
  have eq362529 : ∀ X1 : G, (M.op y y) = (M.op (M.op (M.op y y) (M.op (M.op y y) X1)) (M.op y y)) := by
    intro X1
    first
    | (have i₁ := eq362243 x X1
       have i₂ := eq478 y y x
       grind)
    | exact superpose eq478 eq362243
    | exact resolve eq362243 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362243
  have eq362564 : ∀ X1 : G, (M.op y y) = (M.op (M.op (M.op y y) X1) (M.op y y)) := by
    intro X1
    first
    | (have i₁ := eq362529 X1
       have i₂ := eq475 (M.op y y) X1
       grind)
    | (have i₁ := eq362529 X1
       have i₂ := eq475 (M.op y y) (M.op (M.op y y) X1)
       grind)
    | exact superpose eq475 eq362529
    | exact resolve eq362529 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475 eq362529
  have eq362667 : ∀ X0 : G, (M.op (M.op (M.op y y) (M.op y y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op y y) (M.op y y)
       have i₂ := eq362564 X0
       grind)
    | exact superpose eq362564 eq14
    | exact resolve eq14 eq362564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362564
  have eq362791 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq362667 X0
       have i₂ := eq3322 y
       grind)
    | exact superpose eq3322 eq362667
    | exact resolve eq362667 eq3322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3322 eq362667
  have eq365354 : ∀ X0 X1 : G, (M.op (M.op y y) X0) = (M.op (M.op (M.op (M.op y y) X0) X1) (M.op (M.op y y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq478 (M.op y y) X0 X1
       have i₂ := eq362791 (M.op (M.op (M.op y y) X0) X1)
       grind)
    | exact superpose eq362791 eq478
    | exact resolve eq478 eq362791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq365476 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq365354 X0 X1
       have i₂ := eq362791 X0
       grind)
    | exact superpose eq362791 eq365354
    | exact resolve eq365354 eq362791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362791 eq365354
  have eq366520 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 X0
       have i₂ := eq365476 X0 X1
       grind)
    | exact superpose eq365476 eq14
    | exact resolve eq14 eq365476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370850 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq366520 (σ X0) X1
       have i₂ := eq8760 X0
       grind)
    | exact superpose eq8760 eq366520
    | exact resolve eq366520 eq8760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366520
  have eq412667 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1)) (σ (k y X0))) (σ (M.op x y))) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | exact superpose eq343887 eq5824
    | (have j0 := eq5824 X0 X1
       grind)
    | exact resolve eq5824 eq343887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5824
  have eq412668 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1)) (σ (k y X0))) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | exact superpose eq343887 eq412667
    | (have j0 := eq412667 X0 X1
       grind)
    | exact resolve eq412667 eq343887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343887 eq412667
  have eq412669 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1)) (σ (k y X0))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq412668 X0 X1
       have i₂ := eq8760 X0
       grind)
    | exact superpose eq8760 eq412668
    | (have j0 := eq412668 X0 X1
       grind)
    | exact resolve eq412668 eq8760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8760 eq412668
  have eq412749 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq412669 x X0
       have i₂ := eq103048
       grind)
    | exact superpose eq103048 eq412669
    | (have j0 := eq412669 x x
       grind)
    | exact resolve eq412669 eq103048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103048 eq412669
  have eq412984 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq412749 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq412749
    | (have j0 := eq412749 X0
       grind)
    | exact resolve eq412749 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412749
  have eq413070 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq412984 x
       have i₂ := eq365476 sF2 (M.op sF4 x)
       grind)
    | exact superpose eq365476 eq412984
    | exact resolve eq412984 eq365476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365476 eq412984
  have eq413143 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq343950 eq413070
    | exact resolve eq413070 eq343950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413070
  have eq413183 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq413143
       have r₂ := eq27
       grind)
    | exact resolve eq413143 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413143
  have eq413216 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq413183
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq413183
    | exact resolve eq413183 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413183
  have eq413241 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq343950 eq413216
    | exact resolve eq413216 eq343950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413216
  have eq413256 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq413241
       have r₂ := eq27
       grind)
    | exact resolve eq413241 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413241
  have eq413262 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq413256
       have i₂ := eq3655
       grind)
    | exact superpose eq3655 eq413256
    | exact resolve eq413256 eq3655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3655 eq413256
  have eq413263 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq413262
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq413262
    | exact resolve eq413262 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413262
  have eq413265 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq413263 eq4053
    | exact resolve eq4053 eq413263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4053 eq413263
  have eq413553 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq413265
       have i₂ := eq4121
       grind)
    | exact superpose eq4121 eq413265
    | exact resolve eq413265 eq4121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4121 eq413265
  have eq413575 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq413553
    | exact resolve eq413553 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq413553
  have eq413576 : x = (M.op x x) := by grind
  clear eq413575
  have eq413764 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq370850 x X0
       have i₂ := eq413576
       grind)
    | exact superpose eq413576 eq370850
    | exact resolve eq370850 eq413576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370850 eq413576
  have eq413864 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq413764 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq413764
    | (have j0 := eq413764 X0
       grind)
    | exact resolve eq413764 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq413764
  have eq418375 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq413864 eq343950
    | exact resolve eq343950 eq413864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343950 eq413864
  have eq418780 : False := by grind
  exact eq418780

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxx_pxy_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X2 X1) (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X2 X1) X0) X2 X1
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X3 (M.op (M.op X3 X0) X2)) X0) (M.op (M.op X0 X1) X4)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X0 X1) (M.op X3 (M.op (M.op X3 X0) X2)) X0 X4
       have i₂ := eq53 X0 X3 X2 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op (M.op X0 (M.op (M.op X0 X1) X4)) (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq58 X0 X1 x x X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq58
    | exact resolve eq58 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq156 : ∀ X1 : G, (M.op (M.op X1 X1) X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq53 X1 X1 x X1
       have i₂ := eq64 X1 X1 x
       grind)
    | exact superpose eq64 eq53
    | exact resolve eq53 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq64 X0 X0 X0
       have i₂ := eq156 X0
       grind)
    | exact superpose eq156 eq64
    | exact resolve eq64 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq186 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X1 X1) (M.op (M.op X1 X1) X0)) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (M.op X0 X0) (M.op X0 X0) x
       have i₂ := eq168 X0
       grind)
    | exact superpose eq168 eq64
    | exact resolve eq64 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq168 X0
       grind)
    | exact superpose eq168 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq168 X0
       grind)
    | exact resolve eq12 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq188 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq190 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X1 X1) X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq186 X0 X1
       have i₂ := eq54 X0 X1 X1
       grind)
    | exact superpose eq54 eq186
    | exact resolve eq186 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq186
  have eq218 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (M.op X0 X0)
       have i₂ := eq189 X0 (τ X1)
       grind)
    | exact superpose eq189 eq17
    | exact resolve eq17 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq359 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X0 X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 (M.op X1 X1) (M.op X1 X1) X2
       have i₂ := eq190 X0 X1
       grind)
    | exact superpose eq190 eq53
    | exact resolve eq53 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq360 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X1 X1) (M.op X1 X1)
       have i₂ := eq190 X0 X1
       grind)
    | exact superpose eq190 eq9
    | exact resolve eq9 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq370 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq360 X0 X1
       have i₂ := eq168 X1
       grind)
    | exact superpose eq168 eq360
    | exact resolve eq360 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq371 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq359 X0 X1 X2
       have i₂ := eq168 X1
       grind)
    | exact superpose eq168 eq359
    | exact resolve eq359 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq359
  have eq373 : ∀ X0 X2 : G, (M.op (M.op X0 X2) X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq371 X0 x X2
       have i₂ := eq370 (M.op X0 X2) x
       grind)
    | exact superpose eq370 eq371
    | exact resolve eq371 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq380 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 X1 X0
       have i₂ := eq370 X0 X1
       grind)
    | exact superpose eq370 eq64
    | exact resolve eq64 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq402 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq986 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq402 y x
       grind)
    | exact superpose eq402 eq16
    | (have j1 := eq402 x x
       grind)
    | exact resolve eq16 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1044 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq402 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq1046 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1044 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq2122 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1046 (M.op X0 X0)
       have i₂ := eq189 X0 (M.op X0 X0)
       grind)
    | exact superpose eq189 eq1046
    | (have j0 := eq1046 (M.op X0 X0)
       grind)
    | exact resolve eq1046 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046
  have eq2144 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2122 X0
       have i₂ := eq380 X0 X0
       grind)
    | exact superpose eq380 eq2122
    | (have j0 := eq2122 X0
       grind)
    | exact resolve eq2122 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq2122
  have eq2145 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq2144 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2144
  have eq2209 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq189 (σ (M.op X0 X0)) X1
       have i₂ := eq2145 X0
       grind)
    | exact superpose eq2145 eq189
    | exact resolve eq189 eq2145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq2229 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq370 X1 (σ (M.op X0 X0))
       have i₂ := eq2145 X0
       grind)
    | exact superpose eq2145 eq370
    | exact resolve eq370 eq2145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2145
  have eq2506 : ∀ X1 : G, (M.op X1 X1) = (σ (M.op (τ X1) (τ X1))) := by
    intro X1
    first
    | (have i₁ := eq218 x X1
       have i₂ := eq2209 x X1
       grind)
    | exact superpose eq2209 eq218
    | exact resolve eq218 eq2209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq2209
  have eq2760 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2506 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2506
    | exact resolve eq2506 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2506
  have eq19754 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq986
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq986
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq986 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq19755 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq19754
  have eq19756 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19755
       have i₂ := eq2760 x
       grind)
    | exact superpose eq2760 eq19755
    | exact resolve eq19755 eq2760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19755
  have eq414332 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq373 (σ x) (σ y)
       have i₂ := eq19756
       grind)
    | exact superpose eq19756 eq373
    | exact resolve eq373 eq19756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19756
  have eq414362 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq414332
       have i₂ := eq2760 x
       grind)
    | exact superpose eq2760 eq414332
    | exact resolve eq414332 eq2760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2760 eq414332
  have eq414363 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq414362
  have eq1497553 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq414363
       grind)
    | exact superpose eq414363 eq10
    | exact resolve eq10 eq414363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414363
  have eq1497597 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1497553
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1497553
    | exact resolve eq1497553 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497553
  have eq1497598 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq1497597
  have eq1497648 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq373 x y
       have i₂ := eq1497598
       grind)
    | exact superpose eq1497598 eq373
    | exact resolve eq373 eq1497598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373 eq1497598
  have eq1497699 : x = (M.op x x) := by grind
  clear eq1497648
  have eq1497771 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq370 X0 x
       have i₂ := eq1497699
       grind)
    | exact superpose eq1497699 eq370
    | exact resolve eq370 eq1497699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq1497826 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2229 x X0
       have i₂ := eq1497699
       grind)
    | exact superpose eq1497699 eq2229
    | exact resolve eq2229 eq1497699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2229 eq1497699
  have eq1505309 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1497826 (σ y)
       grind)
    | exact superpose eq1497826 eq16
    | exact resolve eq16 eq1497826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497826
  have eq1505490 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1505309
       have i₂ := eq1497771 y
       grind)
    | exact superpose eq1497771 eq1505309
    | exact resolve eq1505309 eq1497771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497771 eq1505309
  have eq1505491 : False := by grind
  exact eq1505491

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxx_pyy_pxy_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq174 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, y = (M.op (M.op (M.op x (M.op (M.op x y) X0)) (M.op y X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq313 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq34
  have eq542 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op x (M.op (M.op x y) X0)) y) (M.op y X1)) := by
    intro X0 X1
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq544 : ∀ X1 : G, (M.op y X1) = (M.op y (M.op y X1)) := by
    intro X1
    first
    | exact superpose eq174 eq542
    | exact resolve eq542 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq542
  have eq874 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq883 : (M.op x y) = (k x y) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
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
  have eq893 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq904 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq905 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq904 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq907 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq874 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq908 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq907 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq907 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq907 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907
  have eq923 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq908 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq908
    | (have j0 := eq908 (σ X0) X1
       grind)
    | exact resolve eq908 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq1857 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq176 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq176 X0 X1 X2 X3
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1879 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq176 X0 X1 X2 X3
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1883 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1879 X0 x x X3
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq1879
    | exact resolve eq1879 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879
  have eq1888 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq1857 X0 x x X3 X4
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq1857
    | exact resolve eq1857 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1857
  have eq6237 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq883
       grind)
    | exact superpose eq883 eq40
    | exact resolve eq40 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883
  have eq6238 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq6237
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6237
    | exact resolve eq6237 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6237
  have eq6242 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq6238
    | exact resolve eq6238 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6238
  have eq15075 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq176 X0 X0 x X0
       have i₂ := eq1888 X0 X0 x
       grind)
    | exact superpose eq1888 eq176
    | exact resolve eq176 eq1888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq15110 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1888 X0 X0 X0
       have i₂ := eq15075 X0
       grind)
    | exact superpose eq15075 eq1888
    | exact resolve eq1888 eq15075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15075
  have eq15195 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq15110 X0
       grind)
    | exact superpose eq15110 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq15110 X0
       grind)
    | exact resolve eq13 eq15110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15203 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq15195 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15195
  have eq15218 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X1)) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15203 X2 X0
       have i₂ := eq15203 X1 X0
       grind)
    | exact superpose eq15203 eq15203
    | exact resolve eq15203 eq15203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15221 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (k X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15203 X0 X2
       have i₂ := eq15203 X1 X0
       grind)
    | exact superpose eq15203 eq15203
    | exact resolve eq15203 eq15203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15237 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15110 X0
       have i₂ := eq15203 X1 (M.op X0 X0)
       grind)
    | exact superpose eq15203 eq15110
    | exact resolve eq15110 eq15203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15110
  have eq15570 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) ≠ (σ (k (M.op X0 X0) (M.op X1 X1))) ∨ (M.op X2 X2) = (k X2 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq923 (M.op X0 X0) X2
       have i₂ := eq15218 (M.op X0 X0) X0 X1
       grind)
    | (have i₁ := eq923 (M.op X0 X0) X2
       have i₂ := eq15218 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq15218 eq923
    | (have j0 := eq923 (M.op X0 X0) X2
       grind)
    | exact resolve eq923 eq15218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq15653 : ∀ X0 X2 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op X2 X2) = (k X2 (σ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq15570 X0 x X2
       have i₂ := eq15237 X0 x
       grind)
    | exact superpose eq15237 eq15570
    | (have j0 := eq15570 X0 x X2
       grind)
    | exact resolve eq15570 eq15237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15237 eq15570
  have eq15654 : ∀ X0 X2 : G, (M.op X2 X2) = (k X2 (σ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have j0 := eq15653 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15653
  have eq15728 : ∀ X0 X1 X2 : G, (k X0 (M.op X2 X2)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15203 X2 X0
       have i₂ := eq15654 X1 X0
       grind)
    | exact superpose eq15654 eq15203
    | exact resolve eq15203 eq15654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15729 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (k X0 (σ (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15203 X0 X2
       have i₂ := eq15654 X1 X0
       grind)
    | exact superpose eq15654 eq15203
    | exact resolve eq15203 eq15654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15758 : ∀ X0 X1 : G, (k (τ X0) (M.op X1 X1)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq313 X0 (M.op X1 X1)
       have i₂ := eq15654 X1 X0
       grind)
    | exact superpose eq15654 eq313
    | exact resolve eq313 eq15654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq15823 : ∀ X0 : G, (k y (M.op X0 X0)) = (τ (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq47 (M.op X0 X0)
       have i₂ := eq15654 X0 sF3
       grind)
    | exact superpose eq15654 eq47
    | exact resolve eq47 eq15654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq15841 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq15823 x
       have i₂ := eq15203 x y
       grind)
    | exact superpose eq15203 eq15823
    | exact resolve eq15823 eq15203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15823
  have eq15909 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq15841 eq14
    | exact resolve eq14 eq15841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15841
  have eq16103 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq15909
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq15909
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq15909 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16182 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq16103
  have eq16243 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16182
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq16182
    | exact resolve eq16182 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq16182
  have eq16280 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16243
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16243
    | exact resolve eq16243 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16243
  have eq17395 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15221 (τ X0) x X1
       have i₂ := eq15758 X0 x
       grind)
    | exact superpose eq15758 eq15221
    | exact resolve eq15221 eq15758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15221 eq15758
  have eq17832 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 (M.op X1 X1) X0
       have i₂ := eq17395 X1 X0
       grind)
    | exact superpose eq17395 eq38
    | exact resolve eq38 eq17395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq17395
  have eq22141 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6242 eq893
    | exact resolve eq893 eq6242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893 eq6242
  have eq22152 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq22141
       have r₂ := eq27
       grind)
    | exact resolve eq22141 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22141
  have eq22158 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq16280 eq22152
    | exact resolve eq22152 eq16280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22152
  have eq22210 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq22158 eq152
    | exact resolve eq152 eq22158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22158
  have eq22235 : y = (k y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq22210
    | exact resolve eq22210 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22210
  have eq22243 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq905 y
       grind)
    | (have r₁ := eq22235
       have r₂ := eq905 y
       grind)
    | exact resolve eq22235 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22235
  have eq22260 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq22243 eq1883
    | exact resolve eq1883 eq22243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22243
  have eq22266 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq16280 eq22260
    | exact resolve eq22260 eq16280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16280 eq22260
  have eq22293 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq22266 eq152
    | exact resolve eq152 eq22266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq22266
  have eq22317 : y = (k y y) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq22293
    | exact resolve eq22293 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq22293
  have eq22324 : y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq905 y
       grind)
    | (have r₁ := eq22317
       have r₂ := eq905 y
       grind)
    | exact resolve eq22317 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905 eq22317
  have eq22377 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1888 y y x
       have i₂ := eq22324
       grind)
    | exact superpose eq22324 eq1888
    | exact resolve eq1888 eq22324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22381 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq22377 X0
       have i₂ := eq544 X0
       grind)
    | (have i₁ := eq22377 X0
       have i₂ := eq544 (M.op y X0)
       grind)
    | exact superpose eq544 eq22377
    | exact resolve eq22377 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22377
  have eq23054 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq22381 X0
       grind)
    | exact superpose eq22381 eq16
    | exact resolve eq16 eq22381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22381
  have eq23081 : ∀ X0 : G, y = (M.op y x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq22324 eq23054
    | exact resolve eq23054 eq22324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22324 eq23054
  have eq23103 : ∀ X0 : G, y = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1883 y x
       have i₂ := eq23081 X0
       grind)
    | exact superpose eq23081 eq1883
    | (have j1 := eq23081 y
       grind)
    | exact resolve eq1883 eq23081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883 eq23081
  have eq23250 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have j0 := eq23103 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23103
  have eq23251 : y = (M.op y y) := by grind
  clear eq23250
  have eq23296 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq15909
       have i₂ := eq23251
       grind)
    | exact superpose eq23251 eq15909
    | exact resolve eq15909 eq23251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15909
  have eq23304 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq15203 y X0
       have i₂ := eq23251
       grind)
    | exact superpose eq23251 eq15203
    | exact resolve eq15203 eq23251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15203
  have eq23318 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15654 y X0
       have i₂ := eq23251
       grind)
    | exact superpose eq23251 eq15654
    | exact resolve eq15654 eq23251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23321 : ∀ X0 X1 : G, (k X0 (σ y)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15728 X0 y X1
       have i₂ := eq23251
       grind)
    | exact superpose eq23251 eq15728
    | exact resolve eq15728 eq23251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15728
  have eq23330 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq17832 X0 y
       have i₂ := eq23251
       grind)
    | exact superpose eq23251 eq17832
    | exact resolve eq17832 eq23251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17832
  have eq23347 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq1888 y y x
       have i₂ := eq23251
       grind)
    | exact superpose eq23251 eq1888
    | exact resolve eq1888 eq23251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888
  have eq23351 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq23347 X0
       have i₂ := eq544 X0
       grind)
    | (have i₁ := eq23347 X0
       have i₂ := eq544 (M.op y X0)
       grind)
    | exact superpose eq544 eq23347
    | exact resolve eq23347 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544 eq23347
  have eq23367 : ∀ X0 X1 : G, (k X0 (σ y)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23321 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23321
    | (have j0 := eq23321 X0 X1
       grind)
    | exact resolve eq23321 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23321
  have eq23370 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq23318 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23318
    | (have j0 := eq23318 X0
       grind)
    | exact resolve eq23318 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23318
  have eq23380 : (σ y) = (k (σ y) y) := by
    first
    | (have i₁ := eq23296
       have i₂ := eq23304 sF3
       grind)
    | exact superpose eq23304 eq23296
    | exact resolve eq23296 eq23304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23296
  have eq23390 : ∀ X0 X1 : G, (k X0 (k X1 y)) = (k X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq23367 X0 X1
       have i₂ := eq23304 X1
       grind)
    | exact superpose eq23304 eq23367
    | exact resolve eq23367 eq23304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23367
  have eq23394 : (σ y) = (k (σ y) y) := by
    first
    | (have i₁ := eq23380
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23380
    | exact resolve eq23380 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23380
  have eq23515 : ∀ X0 X1 : G, (k X0 y) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15654 X1 X0
       have i₂ := eq23304 X0
       grind)
    | exact superpose eq23304 eq15654
    | exact resolve eq15654 eq23304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15654
  have eq23658 : ∀ X0 X1 : G, (k X0 y) = (k X0 (k (σ X1) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq23515 X0 X1
       have i₂ := eq23330 X1
       grind)
    | exact superpose eq23330 eq23515
    | exact resolve eq23515 eq23330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23515
  have eq23708 : ∀ X0 : G, (k X0 y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq23658 X0 x
       have i₂ := eq23390 X0 (σ x)
       grind)
    | exact superpose eq23390 eq23658
    | exact resolve eq23658 eq23390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23658
  have eq23817 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq23351 X0
       grind)
    | exact superpose eq23351 eq16
    | exact resolve eq16 eq23351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23846 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23817 X0
       have i₂ := eq23251
       grind)
    | exact superpose eq23251 eq23817
    | exact resolve eq23817 eq23251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23251 eq23817
  have eq23870 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq23351 X0
       have i₂ := eq23846 X0
       grind)
    | exact superpose eq23846 eq23351
    | exact resolve eq23351 eq23846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23351
  have eq23934 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 y X1
       have i₂ := eq23846 (M.op (M.op y X0) X1)
       grind)
    | exact superpose eq23846 eq16
    | exact resolve eq16 eq23846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23948 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23934 X0 X1
       have i₂ := eq23846 X0
       grind)
    | exact superpose eq23846 eq23934
    | exact resolve eq23934 eq23846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23934
  have eq24191 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq23870 x
       grind)
    | exact superpose eq23870 eq18
    | (have j1 := eq23870 x
       grind)
    | exact resolve eq18 eq23870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq23870
  have eq24305 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq24191
       grind)
    | exact superpose eq24191 eq24
    | exact resolve eq24 eq24191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq24344 : (σ y) = (k (σ y) (M.op x y)) := by
    first
    | (have i₁ := eq23394
       have i₂ := eq24191
       grind)
    | exact superpose eq24191 eq23394
    | exact resolve eq23394 eq24191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23394
  have eq24346 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23846 X0
       have i₂ := eq24191
       grind)
    | exact superpose eq24191 eq23846
    | exact resolve eq23846 eq24191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23846 eq24191
  have eq25195 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24305 eq20
    | exact resolve eq20 eq24305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq24305
  have eq25993 : ∀ X0 X1 : G, (k X0 (M.op x y)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | exact superpose eq24346 eq15218
    | exact resolve eq15218 eq24346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15218 eq24346
  have eq26105 : ∀ X0 X1 : G, (k X0 (M.op x y)) = (k X0 (k X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq25993 X0 X1
       have i₂ := eq23304 X1
       grind)
    | exact superpose eq23304 eq25993
    | exact resolve eq25993 eq23304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25993
  have eq26146 : ∀ X0 X1 : G, (k X0 (M.op x y)) = (k X0 (k X1 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq26105 X0 X1
       have i₂ := eq23708 X1
       grind)
    | exact superpose eq23708 eq26105
    | exact resolve eq26105 eq23708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26105
  have eq26603 : ∀ X0 X1 X2 : G, (k X0 (σ y)) = (k X0 (k X1 (σ (M.op X2 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15729 X1 X2 X0
       have i₂ := eq23370 X0
       grind)
    | exact superpose eq23370 eq15729
    | exact resolve eq15729 eq23370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15729 eq23370
  have eq26750 : ∀ X0 X1 X2 : G, (k X0 (σ y)) = (k X0 (k X1 (k (σ X2) y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26603 X0 X1 X2
       have i₂ := eq23330 X2
       grind)
    | exact superpose eq23330 eq26603
    | exact resolve eq26603 eq23330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23330 eq26603
  have eq26817 : ∀ X0 X1 : G, (k X0 (σ y)) = (k X0 (k X1 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq26750 X0 X1 x
       have i₂ := eq23390 X1 (σ x)
       grind)
    | exact superpose eq23390 eq26750
    | exact resolve eq26750 eq23390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23390 eq26750
  have eq26853 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq26146 eq26817
    | exact resolve eq26817 eq26146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26146 eq26817
  have eq28092 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq23948 X0 X1
       grind)
    | exact superpose eq23948 eq16
    | exact resolve eq16 eq23948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28137 : ∀ X0 X1 : G, (M.op (k X0 y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28092 X0 X1
       have i₂ := eq23304 X0
       grind)
    | exact superpose eq23304 eq28092
    | exact resolve eq28092 eq23304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23304 eq28092
  have eq28157 : ∀ X0 X1 : G, (M.op (k X0 (σ y)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28137 X0 X1
       have i₂ := eq23708 X0
       grind)
    | exact superpose eq23708 eq28137
    | exact resolve eq28137 eq23708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23708 eq28137
  have eq28175 : ∀ X0 X1 : G, (M.op (k X0 (M.op x y)) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq26853 eq28157
    | exact resolve eq28157 eq26853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26853 eq28157
  have eq28491 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq24344 eq28175
    | exact resolve eq28175 eq24344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24344 eq28175
  have eq28916 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq28491 eq23948
    | exact resolve eq23948 eq28491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23948 eq28491
  have eq29194 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28916 eq26
    | (have j1 := eq28916 (σ x)
       grind)
    | exact resolve eq26 eq28916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq28916
  have eq29322 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq29194 eq27
    | exact resolve eq27 eq29194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq29194
  have eq29340 : False := by grind
  exact eq29340

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxx_x_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq174 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq175 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq178
    | (have j0 := eq178 X0
       grind)
    | exact resolve eq178 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq877 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq880 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq915 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq916 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq917 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq916 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq946 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq877
       grind)
    | exact superpose eq877 eq39
    | exact resolve eq39 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq947 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq946
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq946
    | exact resolve eq946 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq949 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq947
    | exact resolve eq947 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq957 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq949 eq880
    | exact resolve eq880 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880 eq949
  have eq964 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq957
       have r₂ := eq27
       grind)
    | exact resolve eq957 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq970 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq964 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq964
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq964
       grind)
    | exact resolve eq13 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq971 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq970 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq985 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq964
       have i₂ := eq971 sF2
       grind)
    | exact superpose eq971 eq964
    | exact resolve eq964 eq971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964 eq971
  have eq992 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq985
  have eq1000 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq992 eq141
    | exact resolve eq141 eq992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq1005 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq1000
    | exact resolve eq1000 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000
  have eq1008 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq917 x
       grind)
    | (have r₁ := eq1005
       have r₂ := eq917 x
       grind)
    | exact resolve eq1005 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq1013 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 x x X0
       have i₂ := eq1008
       grind)
    | exact superpose eq1008 eq16
    | exact resolve eq16 eq1008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1014 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq1008
       grind)
    | exact superpose eq1008 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq1008
       grind)
    | exact resolve eq13 eq1008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1015 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1014 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq1028 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1008
       have i₂ := eq1015 x
       grind)
    | exact superpose eq1015 eq1008
    | exact resolve eq1008 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1041 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1028
  have eq1049 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq1041
       grind)
    | exact superpose eq1041 eq39
    | exact resolve eq39 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1041
  have eq1054 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1049
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1049
    | exact resolve eq1049 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq1060 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1054 eq917
    | (have j0 := eq917 (σ x)
       grind)
    | (have r₁ := eq917 (σ x)
       have r₂ := eq1054
       grind)
    | exact resolve eq917 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917 eq1054
  have eq1061 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1060
  have eq1069 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1061 eq16
    | exact resolve eq16 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1070 : (σ x) = (k (σ x) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1061 eq1015
    | exact resolve eq1015 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061
  have eq1075 : (σ x) = (k (σ x) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1070
  have eq1291 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq176 X0 X1 X2 X3
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1296 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1291 X0 x x X3
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq1291
    | exact resolve eq1291 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291
  have eq1562 : x = (M.op (M.op x (M.op x y)) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1013 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1013
    | (have j0 := eq1013 y
       grind)
    | exact resolve eq1013 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq1606 : (M.op x y) = (M.op (M.op x x) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1562 eq16
    | exact resolve eq16 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1613 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1008 eq1606
    | exact resolve eq1606 eq1008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606
  have eq1617 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1613 eq1562
    | exact resolve eq1562 eq1613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562 eq1613
  have eq1627 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1617
  have eq1632 : y = (M.op (M.op x x) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1627 eq174
    | exact resolve eq174 eq1627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1627
  have eq1640 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1008 eq1632
    | exact resolve eq1632 eq1008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008 eq1632
  have eq1642 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1640
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1640
    | exact resolve eq1640 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1640
  have eq1646 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1642 eq175
    | exact resolve eq175 eq1642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1649 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1646 X0
       have i₂ := eq1296 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq1646 x
       have i₂ := eq1296 sF2 x
       grind)
    | exact superpose eq1296 eq1646
    | exact resolve eq1646 eq1296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq1660 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1649 eq176
    | exact resolve eq176 eq1649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1661 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1649 eq16
    | exact resolve eq16 eq1649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649
  have eq1674 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq1661
    | (have j0 := eq1661 X0
       grind)
    | exact resolve eq1661 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1661
  have eq1675 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq26 eq1660
    | (have j0 := eq1660 X0 X1
       grind)
    | exact resolve eq1660 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1660
  have eq1678 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1642 eq1674
    | exact resolve eq1674 eq1642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674
  have eq1679 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op X0 X1)) X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1642 eq1675
    | exact resolve eq1675 eq1642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1642 eq1675
  have eq1681 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1678 eq1679
    | exact resolve eq1679 eq1678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1679
  have eq1794 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1678 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1678 (σ x)
       grind)
    | exact resolve eq13 eq1678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1795 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1794 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1794
  have eq1911 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq1681 X0 X1
       grind)
    | exact superpose eq1681 eq16
    | exact resolve eq16 eq1681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1681
  have eq1937 : ∀ X0 X1 : G, (M.op (k X0 (σ x)) X1) = X1 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1795 eq1911
    | exact resolve eq1911 eq1795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1911
  have eq2511 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1678 sF2
       have i₂ := eq1795 sF2
       grind)
    | exact superpose eq1795 eq1678
    | exact resolve eq1678 eq1795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1678
  have eq2519 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2511
  have eq2556 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2519 eq141
    | exact resolve eq141 eq2519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq2519
  have eq2566 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq2556
    | exact resolve eq2556 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2556
  have eq2576 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq915 x x
       have i₂ := eq2566
       grind)
    | exact superpose eq2566 eq915
    | (have j0 := eq915 x x
       grind)
    | (have r₁ := eq915 x x
       have r₂ := eq2566
       grind)
    | exact resolve eq915 eq2566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2566
  have eq2577 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2576
  have eq2578 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2577
  have eq2593 : x = (k x (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1795 x
       have i₂ := eq2578
       grind)
    | exact superpose eq2578 eq1795
    | exact resolve eq1795 eq2578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795 eq2578
  have eq2608 : x = (k x (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2593
  have eq2651 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2608 eq1937
    | exact resolve eq1937 eq2608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1937 eq2608
  have eq2699 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2651 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2651
  have eq2717 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2699 y
       grind)
    | exact superpose eq2699 eq18
    | (have j1 := eq2699 y
       grind)
    | exact resolve eq18 eq2699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2699
  have eq2742 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2717
  have eq2756 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2742
       grind)
    | exact superpose eq2742 eq24
    | exact resolve eq24 eq2742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2742
  have eq2768 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2756
    | exact resolve eq2756 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2756
  have eq3760 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1069
    | (have j0 := eq1069 (σ y)
       grind)
    | exact resolve eq1069 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq3832 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3760 eq16
    | exact resolve eq16 eq3760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3848 : (M.op (σ x) (σ y)) = (M.op (k (σ x) x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1015 eq3832
    | exact resolve eq3832 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3832
  have eq3852 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1075 eq3848
    | exact resolve eq3848 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3848
  have eq3857 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3852 eq3760
    | exact resolve eq3760 eq3852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3760 eq3852
  have eq3876 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3857
  have eq3883 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3876 eq175
    | exact resolve eq175 eq3876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3876
  have eq3899 : (σ y) = (M.op (k (σ x) x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1015 eq3883
    | exact resolve eq3883 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015 eq3883
  have eq3903 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1075 eq3899
    | exact resolve eq3899 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075 eq3899
  have eq3905 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3903
    | exact resolve eq3903 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3903
  have eq3906 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3905 eq27
    | exact resolve eq27 eq3905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3905
  have eq3928 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3906
       have r₂ := eq2768
       grind)
    | exact resolve eq3906 eq2768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3906
  have eq3933 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3928 eq27
    | exact resolve eq27 eq3928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3934 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3928 eq175
    | exact resolve eq175 eq3928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq3941 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3934 X0
       have i₂ := eq1296 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq3934 x
       have i₂ := eq1296 sF2 x
       grind)
    | exact superpose eq1296 eq3934
    | exact resolve eq3934 eq1296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1296 eq3934
  have eq3942 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2768 eq3933
    | exact resolve eq3933 eq2768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2768 eq3933
  have eq3945 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq3942
  have eq3957 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq3941
    | (have j0 := eq3941 (σ y)
       grind)
    | exact resolve eq3941 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3941
  have eq4003 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3928 eq3957
    | exact resolve eq3957 eq3928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3957
  have eq4007 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq4003
    | exact resolve eq4003 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4003
  have eq4010 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3928 eq4007
    | exact resolve eq4007 eq3928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3928 eq4007
  have eq4012 : x = (M.op x y) := by
    first
    | (have r₁ := eq4010
       have r₂ := eq3945
       grind)
    | exact resolve eq4010 eq3945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3945 eq4010
  have eq4013 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4012
       grind)
    | exact superpose eq4012 eq18
    | exact resolve eq18 eq4012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4014 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq4012
       grind)
    | exact superpose eq4012 eq22
    | exact resolve eq22 eq4012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq4017 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) y) := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq4012
       grind)
    | exact superpose eq4012 eq174
    | exact resolve eq174 eq4012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq4012
  have eq4023 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq180 eq4017
    | exact resolve eq4017 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4017
  have eq4025 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4014 eq20
    | exact resolve eq20 eq4014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4144 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4013 eq180
    | exact resolve eq180 eq4013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq4177 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op X0 X0) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq4144 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq4144
       grind)
    | exact resolve eq13 eq4144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4186 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq4177 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4177
  have eq4201 : y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq4144 eq4023
    | exact resolve eq4023 eq4144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4144
  have eq4216 : ∀ X0 : G, (M.op (M.op (M.op x y) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq4023 eq16
    | exact resolve eq16 eq4023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4023
  have eq4231 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq4013 eq4216
    | exact resolve eq4216 eq4013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4216
  have eq4235 : y = (M.op x y) := by
    first
    | exact superpose eq4013 eq4201
    | exact resolve eq4201 eq4013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4013 eq4201
  have eq4241 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq4235
       grind)
    | exact superpose eq4235 eq24
    | exact resolve eq24 eq4235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4235
  have eq4259 : (σ x) = (σ y) := by
    first
    | exact superpose eq4014 eq4241
    | exact resolve eq4241 eq4014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4014 eq4241
  have eq4266 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4259 eq26
    | exact resolve eq26 eq4259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4259
  have eq4315 : (M.op (σ x) (σ y)) = (k (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq4266
       have i₂ := eq4186 sF2
       grind)
    | exact superpose eq4186 eq4266
    | exact resolve eq4266 eq4186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4266
  have eq4891 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq4231 sF0
       have i₂ := eq4186 sF0
       grind)
    | exact superpose eq4186 eq4231
    | exact resolve eq4231 eq4186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4231
  have eq4926 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq4891 eq37
    | exact resolve eq37 eq4891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq4891
  have eq4938 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq4926
    | exact resolve eq4926 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4926
  have eq4940 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4025 eq4938
    | exact resolve eq4938 eq4025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4938
  have eq4949 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4940 eq915
    | (have j0 := eq915 (σ x) (σ x)
       grind)
    | (have r₁ := eq915 (σ x) (σ x)
       have r₂ := eq4940
       grind)
    | exact resolve eq915 eq4940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915 eq4940
  have eq4950 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4949
  have eq4951 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4950
  have eq4955 : (σ x) = (k (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq4951
       have i₂ := eq4186 sF2
       grind)
    | exact superpose eq4186 eq4951
    | exact resolve eq4951 eq4186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4186 eq4951
  have eq4966 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4955 eq4315
    | exact resolve eq4315 eq4955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4315 eq4955
  have eq4977 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq4966 eq27
    | exact resolve eq27 eq4966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4966
  have eq4991 : False := by grind
  exact eq4991

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_pyy_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq18
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq69 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq69
    | exact resolve eq69 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq72 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq66 X0 x x X3 X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq66
    | exact resolve eq66 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq177 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61 X0 X0 x X0
       have i₂ := eq72 X0 X0 x
       grind)
    | exact superpose eq72 eq61
    | exact resolve eq61 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq188 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq72 X0 X0 X0
       have i₂ := eq177 X0
       grind)
    | exact superpose eq177 eq72
    | exact resolve eq72 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq177
  have eq204 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op X0 X0) X1
       have i₂ := eq188 X0
       grind)
    | exact superpose eq188 eq9
    | exact resolve eq9 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq188 X0
       grind)
    | exact superpose eq188 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq188 X0
       grind)
    | exact resolve eq12 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq206 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq208 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq204 X0 X1
       have i₂ := eq71 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq204 X0 X1
       have i₂ := eq71 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq71 eq204
    | exact resolve eq204 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq254 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq208 X0 X1
       grind)
    | exact superpose eq208 eq9
    | exact resolve eq9 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq261 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq254 X0 X1
       have i₂ := eq188 X0
       grind)
    | exact superpose eq188 eq254
    | exact resolve eq254 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq254
  have eq266 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq207 X0 X1
       have i₂ := eq261 X0 X1
       grind)
    | exact superpose eq261 eq207
    | exact resolve eq207 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq261
  have eq312 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op X1 X1)
       have i₂ := eq266 X1 (σ X0)
       grind)
    | exact superpose eq266 eq28
    | exact resolve eq28 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq323 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq312 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq312
    | exact resolve eq312 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq519 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq519 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq519
    | (have j0 := eq519 (σ X0) (σ X1)
       grind)
    | exact resolve eq519 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2218 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq564 X1 X0
       have i₂ := eq519 X1 X0
       grind)
    | exact superpose eq519 eq564
    | (have j0 := eq564 X1 X0
       have j1 := eq519 (σ X1) (σ X0)
       grind)
    | exact resolve eq564 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq15890 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2218 x y
       grind)
    | exact superpose eq2218 eq16
    | (have j1 := eq2218 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2218 x y
       grind)
    | exact resolve eq16 eq2218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2218
  have eq15945 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15890
  have eq15979 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq71 (σ x) (σ y)
       have i₂ := eq15945
       grind)
    | exact superpose eq15945 eq71
    | exact resolve eq71 eq15945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15945
  have eq16027 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq323 X0 (σ x)
       have i₂ := eq15979
       grind)
    | exact superpose eq15979 eq323
    | exact resolve eq323 eq15979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq16089 : ∀ X0 : G, x = (M.op x y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq16027 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16027
    | exact resolve eq16027 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16027
  have eq16104 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq71 x y
       have i₂ := eq16089 X0
       grind)
    | exact superpose eq16089 eq71
    | (have j1 := eq16089 X0
       grind)
    | exact resolve eq71 eq16089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq16089
  have eq16146 : ∀ X0 X1 : G, (k X1 x) = X1 ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq266 x X1
       have i₂ := eq16104 X0
       grind)
    | exact superpose eq16104 eq266
    | (have j1 := eq16104 X1
       grind)
    | exact resolve eq266 eq16104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq16104
  have eq16539 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq16146 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16146
  have eq16540 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq16539 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16539
  have eq16581 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16540 X0
       have i₂ := eq519 X0 x
       grind)
    | exact superpose eq519 eq16540
    | (have j1 := eq519 X0 x
       grind)
    | exact resolve eq16540 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16658 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq17 X0 x
       have i₂ := eq16540 (τ X0)
       grind)
    | exact superpose eq16540 eq17
    | exact resolve eq17 eq16540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq16663 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16658 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16658
    | exact resolve eq16658 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16658
  have eq16877 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16663 X0
       have i₂ := eq519 X0 (σ x)
       grind)
    | exact superpose eq519 eq16663
    | (have j1 := eq519 X0 (σ x)
       grind)
    | exact resolve eq16663 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq18058 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq16581 x
       grind)
    | exact superpose eq16581 eq12
    | (have j0 := eq12 X0 x
       have j1 := eq16581 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq16581 x
       grind)
    | exact resolve eq12 eq16581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16581
  have eq18118 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq18058 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18058
  have eq18141 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq18118 X0
       have j1 := eq12 X0 x
       grind)
    | (have r₁ := eq18118 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq18118 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18118
  have eq18146 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18141 X0
       have i₂ := eq16540 X0
       grind)
    | exact superpose eq16540 eq18141
    | exact resolve eq18141 eq16540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16540 eq18141
  have eq18148 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq15979
       have i₂ := eq18146 y
       grind)
    | exact superpose eq18146 eq15979
    | exact resolve eq15979 eq18146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15979
  have eq18150 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18146 y
       grind)
    | exact superpose eq18146 eq16
    | exact resolve eq16 eq18146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18146
  have eq18864 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq18148
       grind)
    | exact superpose eq18148 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq18148
       grind)
    | exact resolve eq12 eq18148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18148
  have eq18910 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq18864 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18864
  have eq18935 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq18910 X0
       have i₂ := eq16663 X0
       grind)
    | exact superpose eq16663 eq18910
    | exact resolve eq18910 eq16663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16663 eq18910
  have eq18944 : (σ y) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq18150
       have i₂ := eq18935 (σ y)
       grind)
    | exact superpose eq18935 eq18150
    | (have r₁ := eq18150
       have r₂ := eq18935 (σ y)
       grind)
    | exact resolve eq18150 eq18935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18935
  have eq19009 : x = y := by grind
  clear eq18944
  have eq19090 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq18150
       have i₂ := eq19009
       grind)
    | exact superpose eq19009 eq18150
    | exact resolve eq18150 eq19009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18150 eq19009
  have eq21443 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq19090
       have i₂ := eq16877 (σ x)
       grind)
    | exact superpose eq16877 eq19090
    | (have j1 := eq16877 (σ x)
       grind)
    | (have r₁ := eq19090
       have r₂ := eq16877 (σ x)
       grind)
    | exact resolve eq19090 eq16877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16877
  have eq21518 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq21443
  have eq21561 : False := by grind
  exact eq21561

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq90 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq69
       have i₂ := eq90 y x
       grind)
    | exact superpose eq90 eq69
    | (have j1 := eq90 y x
       grind)
    | exact resolve eq69 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq116 eq90
    | (have j0 := eq90 (σ y) (σ x)
       grind)
    | exact resolve eq90 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq119
    | exact resolve eq119 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq123 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq120
       have r₂ := eq27
       grind)
    | exact resolve eq120 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq125 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq123
    | exact resolve eq123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq220 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq125 eq51
    | exact resolve eq51 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq225 : (σ y) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq220
    | (have j0 := eq220 (σ y)
       grind)
    | exact resolve eq220 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq231 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq225 eq14
    | exact resolve eq14 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq235 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq231
    | exact resolve eq231 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq259 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq125 eq235
    | exact resolve eq235 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq235
  have eq264 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq259
  have eq267 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq264 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq264
       grind)
    | exact resolve eq13 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq268 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq267 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq581 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq268 eq116
    | exact resolve eq116 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq268
  have eq584 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq581
  have eq589 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq584
    | exact resolve eq584 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq591 : x = (M.op x y) := by
    first
    | (have r₁ := eq589
       have r₂ := eq27
       grind)
    | exact resolve eq589 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq593 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq591 eq20
    | exact resolve eq20 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : ∀ X0 : G, y = (M.op (M.op x (M.op x X0)) y) := by
    intro X0
    first
    | exact superpose eq591 eq50
    | exact resolve eq50 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq607 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq593
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq593
    | exact resolve eq593 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq608 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq607 eq26
    | exact resolve eq26 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq705 : y = (M.op (M.op x (M.op x y)) y) := by
    first
    | (have i₁ := eq595 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq595
    | (have j0 := eq595 y
       grind)
    | exact resolve eq595 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq719 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq591 eq705
    | exact resolve eq705 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq730 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq14 x x y
       have i₂ := eq719
       grind)
    | exact superpose eq719 eq14
    | exact resolve eq14 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq737 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq730
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq730
    | exact resolve eq730 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq740 : x = (M.op x x) := by
    first
    | exact superpose eq591 eq737
    | exact resolve eq737 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq751 : y = (M.op x y) := by
    first
    | (have i₁ := eq719
       have i₂ := eq740
       grind)
    | exact superpose eq740 eq719
    | exact resolve eq719 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq759 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq740
       grind)
    | exact superpose eq740 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq740
       grind)
    | exact resolve eq13 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq760 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq759 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq763 : y = (M.op x y) := by
    first
    | (have i₁ := eq751
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq751
    | exact resolve eq751 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq765 : x = y := by
    first
    | exact superpose eq591 eq763
    | exact resolve eq763 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591 eq763
  have eq767 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq765
       grind)
    | exact superpose eq765 eq24
    | exact resolve eq24 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq765
  have eq784 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq767
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq767
    | exact resolve eq767 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq767
  have eq791 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq607 eq784
    | exact resolve eq784 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq815 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq791 eq608
    | exact resolve eq608 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq850 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq760 y
       grind)
    | exact superpose eq760 eq69
    | exact resolve eq69 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq760
  have eq855 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq607 eq850
    | exact resolve eq850 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607 eq850
  have eq859 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq791 eq855
    | exact resolve eq855 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791 eq855
  have eq862 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq859
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq859
    | exact resolve eq859 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq859
  have eq865 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq862
    | exact resolve eq862 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq862
  have eq873 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq865 eq90
    | (have j0 := eq90 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq90 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq865
  have eq874 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq873
  have eq876 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq815 eq874
    | exact resolve eq874 eq815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815 eq874
  have eq879 : False := by grind
  exact eq879
