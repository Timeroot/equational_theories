import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pyy_x_pxy_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
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
  have eq46 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq47 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
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
  have eq54 : (k x x) = (τ (k (σ x) (σ x))) := by
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
  have eq62 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 (M.op (M.op X1 X0) X2)) = (M.op X0 X0) ∨ (M.op X1 (M.op (M.op X1 X0) X2)) = (k (M.op X1 (M.op (M.op X1 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X1 (M.op (M.op X1 X0) X2)) X0
       grind)
    | (have r₁ := eq12 (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 X0) X2)) = (k (M.op X1 (M.op (M.op X1 X0) X2)) X0) ∨ (M.op X1 (M.op (M.op X1 X0) X2)) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq65 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq74
    | exact resolve eq74 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq83
    | exact resolve eq83 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq85
    | exact resolve eq85 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq117 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq158 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq117 eq16
    | exact resolve eq16 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq172 : (σ (k (k x (M.op x y)) y)) = (k (k (σ x) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq46 eq41
    | exact resolve eq41 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq463 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq49 X0 X1 X2 X3
       grind)
    | exact superpose eq49 eq49
    | exact resolve eq49 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq49 x X0 X1 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq49
    | (have j0 := eq49 x X0 X1 y
       grind)
    | exact resolve eq49 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq49 X0 X1 X2 X3
       grind)
    | exact superpose eq49 eq14
    | exact resolve eq14 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq474 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq474
    | exact resolve eq474 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq481 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq463 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq463
    | exact resolve eq463 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq487 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq478 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq478
    | (have j0 := eq478 x y
       grind)
    | exact resolve eq478 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq489 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq478
    | (have j0 := eq478 (σ x) (σ y)
       grind)
    | exact resolve eq478 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq512 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq489 eq14
    | exact resolve eq14 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq762 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = (k (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) ∨ (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = (M.op (M.op X0 X3) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq66 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq49 X0 X1 X2 X3
       grind)
    | exact superpose eq49 eq66
    | exact resolve eq66 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq778 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op X0 X3)) = X0 ∨ (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = (M.op (M.op X0 X3) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq762 X0 X1 X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq762
    | (have j0 := eq762 X0 X1 X2 X3
       grind)
    | exact resolve eq762 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq783 : ∀ X0 X3 : G, (M.op (M.op X0 X3) (M.op X0 X3)) = X0 ∨ (k X0 (M.op X0 X3)) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq778 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq778
    | (have j0 := eq778 X0 x x X3
       grind)
    | exact resolve eq778 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq3327 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq49 X0 X0 x X0
       have i₂ := eq481 X0 X0 x
       grind)
    | exact superpose eq481 eq49
    | exact resolve eq49 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq481
  have eq3366 : x = (M.op (M.op (M.op x x) (M.op x y)) x) := by
    first
    | (have i₁ := eq470 x x
       have i₂ := eq3327 x
       grind)
    | exact superpose eq3327 eq470
    | exact resolve eq470 eq3327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq3571 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    grind
  clear eq783
  have eq3579 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3571 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3571
  have eq3608 : x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq3579 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3579
    | (have j0 := eq3579 x y
       grind)
    | exact resolve eq3579 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3611 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq3579
    | (have j0 := eq3579 (σ x) (σ y)
       grind)
    | exact resolve eq3579 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3579
  have eq3641 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq3608 eq46
    | exact resolve eq46 eq3608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3655 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3641
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3641
    | exact resolve eq3641 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3641
  have eq4662 : (σ (k (k x (M.op x y)) y)) = (M.op (k (σ x) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (k (σ x) (σ (M.op x y))) (σ y)) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq46 eq182
    | exact resolve eq182 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq182
  have eq4730 : (M.op (σ x) (σ y)) = (σ (k (k x (M.op x y)) y)) ∨ (σ y) = (M.op (k (σ x) (σ (M.op x y))) (σ y)) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3655 eq4662
    | exact resolve eq4662 eq3655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4662
  have eq4746 : (M.op (σ x) (σ y)) = (k (k (σ x) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (k (σ x) (σ (M.op x y))) (σ y)) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq172 eq4730
    | exact resolve eq4730 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq4730
  have eq4755 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (k (σ x) (σ (M.op x y))) (σ y)) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3655 eq4746
    | exact resolve eq4746 eq3655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4746
  have eq4762 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (k (σ x) (σ (M.op x y))) (σ y)) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq4755
    | exact resolve eq4755 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4755
  have eq4769 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3655 eq4762
    | exact resolve eq4762 eq3655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4762
  have eq4774 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq4769
    | exact resolve eq4769 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4769
  have eq4776 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3655 eq4774
    | exact resolve eq4774 eq3655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4774
  have eq16698 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq86 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16705 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq16698
    | exact resolve eq16698 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16698
  have eq16716 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq16705
       have r₂ := eq28
       grind)
    | exact resolve eq16705 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16705
  have eq16719 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq16716
    | exact resolve eq16716 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16716
  have eq16728 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16719 eq3327
    | exact resolve eq3327 eq16719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16719
  have eq16755 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq16728
    | exact resolve eq16728 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16728
  have eq16756 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16755
  have eq16764 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3327 y
       have i₂ := eq16756
       grind)
    | exact superpose eq16756 eq3327
    | exact resolve eq3327 eq16756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16756
  have eq16791 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16764
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16764
    | exact resolve eq16764 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16764
  have eq16792 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq16791
  have eq16814 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16792 eq3611
    | exact resolve eq3611 eq16792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3611 eq16792
  have eq16963 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16814 eq86
    | exact resolve eq86 eq16814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq16814
  have eq16976 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq16963
  have eq17567 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3327 y
       have i₂ := eq16976
       grind)
    | exact superpose eq16976 eq3327
    | exact resolve eq3327 eq16976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16976
  have eq17594 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq17567
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17567
    | exact resolve eq17567 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17567
  have eq17595 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq17594
  have eq17667 : (k x x) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17595 eq54
    | exact resolve eq54 eq17595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq17671 : (k x (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17595 eq62
    | exact resolve eq62 eq17595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq17595
  have eq17766 : (k x (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq158 eq17671
    | exact resolve eq17671 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17671
  have eq17768 : (k x x) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq158 eq17667
    | exact resolve eq17667 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq17667
  have eq17772 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3608 eq17766
    | exact resolve eq17766 eq3608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3608 eq17766
  have eq20495 : x = (k x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17768 eq17772
    | exact resolve eq17772 eq17768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17768 eq17772
  have eq20514 : x = (k x x) ∨ y = (M.op x y) := by grind
  clear eq20495
  have eq20565 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq20514
       grind)
    | exact superpose eq20514 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq20514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20514
  have eq20577 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq20565
  have eq20676 : x = (M.op (M.op x (M.op x y)) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3366
       have i₂ := eq20577
       grind)
    | exact superpose eq20577 eq3366
    | exact resolve eq3366 eq20577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3366
  have eq20727 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq487 eq20676
    | exact resolve eq20676 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487 eq20676
  have eq20909 : y = (M.op (M.op x x) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20727 eq47
    | exact resolve eq47 eq20727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq20727
  have eq30492 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20909
       have i₂ := eq20577
       grind)
    | exact superpose eq20577 eq20909
    | exact resolve eq20909 eq20577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20577 eq20909
  have eq30530 : y = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq30492
  have eq30545 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq30530
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq30530
    | exact resolve eq30530 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq30530
  have eq30546 : y = (M.op x y) := by grind
  clear eq30545
  have eq30549 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq30546 eq21
    | exact resolve eq21 eq30546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq30546
  have eq30695 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq30549
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq30549
    | exact resolve eq30549 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq30549
  have eq30704 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq30695 eq27
    | exact resolve eq27 eq30695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq30772 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq30695 eq4776
    | exact resolve eq4776 eq30695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4776 eq30695
  have eq30804 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq30772
       have r₂ := eq28
       grind)
    | exact resolve eq30772 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30772
  have eq30862 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3655 eq30804
    | exact resolve eq30804 eq3655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3655 eq30804
  have eq32348 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30862 eq3327
    | exact resolve eq3327 eq30862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3327 eq30862
  have eq32375 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30704 eq32348
    | exact resolve eq32348 eq30704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32348
  have eq32376 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq32375
       have r₂ := eq28
       grind)
    | exact resolve eq32375 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32375
  have eq32388 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32376 eq489
    | exact resolve eq489 eq32376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq32389 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq32376 eq512
    | exact resolve eq512 eq32376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512 eq32376
  have eq32413 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq32389 X0
       have i₂ := eq478 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq32389 x
       have i₂ := eq478 sF2 x
       grind)
    | exact superpose eq478 eq32389
    | exact resolve eq32389 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478 eq32389
  have eq33407 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq32413 eq14
    | exact resolve eq14 eq32413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32413
  have eq33473 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq32388 eq33407
    | exact resolve eq33407 eq32388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32388 eq33407
  have eq33506 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33473 eq30704
    | exact resolve eq30704 eq33473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30704 eq33473
  have eq33614 : False := by grind
  exact eq33614

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pyx_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq67 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq23 eq37
  have eq84 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq11 X0 (M.op X1 (M.op X0 X0))
       have r₂ := eq13 (M.op X0 X0) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq84 y x
       grind)
    | exact superpose eq84 eq76
    | (have j1 := eq84 y x
       grind)
    | exact resolve eq76 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq103
    | exact resolve eq103 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq113
    | exact resolve eq113 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq423 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq431 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq423 X0
       grind)
    | exact superpose eq423 eq13
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq423 X0
       grind)
    | exact resolve eq13 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq438 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq431 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq825 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq114 eq84
    | (have j0 := eq84 (σ y) (σ x)
       grind)
    | exact resolve eq84 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq826 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq825
    | exact resolve eq825 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq829 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq826
       have r₂ := eq28
       grind)
    | exact resolve eq826 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq843 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq829 eq423
    | exact resolve eq423 eq829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq846 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq843
    | exact resolve eq843 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq858 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq438 y
       have i₂ := eq846
       grind)
    | exact superpose eq846 eq438
    | exact resolve eq438 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq859 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq423 y
       have i₂ := eq846
       grind)
    | exact superpose eq846 eq423
    | exact resolve eq423 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq862 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq859
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq859
    | exact resolve eq859 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq878 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq862 eq28
    | exact resolve eq28 eq862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq881 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq862 eq67
    | (have r₁ := eq67
       have r₂ := eq862
       grind)
    | exact resolve eq67 eq862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq862
  have eq888 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq881
  have eq890 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq858
       grind)
    | exact superpose eq858 eq76
    | exact resolve eq76 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq858
  have eq892 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq890
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq890
    | exact resolve eq890 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq910 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq888 eq114
    | exact resolve eq114 eq888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq888
  have eq915 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq910
       have r₂ := eq878
       grind)
    | exact resolve eq910 eq878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878 eq910
  have eq964 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq423 y
       have i₂ := eq915
       grind)
    | exact superpose eq915 eq423
    | exact resolve eq423 eq915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq966 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq964
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq964
    | exact resolve eq964 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq964
  have eq967 : y = (M.op x y) := by grind
  clear eq966
  have eq968 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq967 eq21
    | exact resolve eq21 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq967
  have eq997 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq968
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq968
    | exact resolve eq968 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq968
  have eq998 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq997 eq27
    | exact resolve eq27 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1018 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq997 eq892
    | exact resolve eq892 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892 eq997
  have eq1020 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq1018
       have r₂ := eq28
       grind)
    | exact resolve eq1018 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018
  have eq1057 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1020 eq84
    | (have j0 := eq84 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq84 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq1020
  have eq1058 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq998 eq1057
    | exact resolve eq1057 eq998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1061 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq1058
       have r₂ := eq28
       grind)
    | exact resolve eq1058 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058
  have eq1095 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1061 eq423
    | exact resolve eq423 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423 eq1061
  have eq1097 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq998 eq1095
    | exact resolve eq1095 eq998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998 eq1095
  have eq1098 : False := by grind
  exact eq1098
