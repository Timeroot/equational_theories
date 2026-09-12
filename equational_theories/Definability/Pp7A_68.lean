import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3607`: `x ◇ y = z ◇ ((y ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation3607 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3607 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3607.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 : G, (k (τ (σ X0)) X0) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq12 (τ (σ X0)) X0
       grind)
    | (have r₁ := eq12 (τ (σ X0)) X0
       have r₂ := eq10 X0
       grind)
    | (have r₁ := eq12 X0 (τ (σ X0))
       have r₂ := eq10 X0
       grind)
    | exact resolve eq12 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq17 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17
    | exact resolve eq17 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq29 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq15
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq37
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq37
  have eq102 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq115 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq1549 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq115 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq1552 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1549 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq1549 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq1549 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq1549 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq1549 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549
  have eq1577 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 X0
       have i₂ := eq1552 X0 (τ X1)
       grind)
    | exact superpose eq1552 eq29
    | (have j1 := eq1552 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq29 eq1552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1578 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1552 (σ X0) (σ X1)
       grind)
    | exact superpose eq1552 eq15
    | (have j1 := eq1552 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq1552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552
  have eq3049 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1577 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1577
    | exact resolve eq1577 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1577
  have eq3092 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3049 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3049
    | (have j0 := eq3049 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq3049 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3049
  have eq63806 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1578 x y
       grind)
    | exact superpose eq1578 eq16
    | (have j1 := eq1578 x y
       grind)
    | exact resolve eq16 eq1578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1578
  have eq64468 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq63806
       have i₂ := eq3092 y x
       grind)
    | exact superpose eq3092 eq63806
    | (have j1 := eq3092 (σ x) (σ y)
       grind)
    | (have r₁ := eq63806
       have r₂ := eq3092 y x
       grind)
    | (have r₁ := eq63806
       have r₂ := eq3092 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq63806
       have r₂ := eq3092 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq63806 eq3092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3092 eq63806
  have eq64469 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq64468
  have eq64642 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq64469
       grind)
    | exact superpose eq64469 eq10
    | exact resolve eq10 eq64469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64469
  have eq64700 : x = y ∨ x = y := by
    first
    | (have i₁ := eq64642
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq64642
    | exact resolve eq64642 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64642
  have eq64701 : x = y := by grind
  clear eq64700
  have eq65082 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq64701
       grind)
    | exact superpose eq64701 eq16
    | exact resolve eq16 eq64701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64701
  have eq65083 : False := by grind
  exact eq65083

/-- `Equation3607`: `x ◇ y = z ◇ ((y ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation3607 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3607 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3607.models_iff G M).mp hM
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq69 : x ≠ (M.op x y) ∨ x = y ∨ x = (k x y) := by
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
  have eq70 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq78
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq78
    | exact resolve eq78 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq84
    | exact resolve eq84 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq86
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq86
    | exact resolve eq86 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq732 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq87 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq733 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq732
    | exact resolve eq732 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq736 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq733
       have r₂ := eq28
       grind)
    | exact resolve eq733 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq738 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq736
    | exact resolve eq736 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq740 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq738 eq70
    | (have r₁ := eq70
       have r₂ := eq738
       grind)
    | exact resolve eq70 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq742 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq738 eq28
    | exact resolve eq28 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq743 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq740
  have eq744 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq743
  have eq757 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq744 eq87
    | exact resolve eq87 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq744
  have eq761 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq757
  have eq766 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq761
       have r₂ := eq742
       grind)
    | exact resolve eq761 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq761
  have eq837 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq766 eq30
    | exact resolve eq30 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq856 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq837
    | exact resolve eq837 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq857 : x = (M.op x y) ∨ x = y := by grind
  clear eq856
  have eq860 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq857 eq21
    | exact resolve eq21 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq863 : x ≠ x ∨ x = y ∨ x = (k x y) ∨ x = y := by
    first
    | exact superpose eq857 eq69
    | (have r₁ := eq69
       have r₂ := eq857
       grind)
    | exact resolve eq69 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq857
  have eq871 : x ≠ x ∨ x = y ∨ x = (k x y) := by grind
  clear eq863
  have eq872 : x = (k x y) ∨ x = y := by grind
  clear eq871
  have eq881 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq860
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq860
    | exact resolve eq860 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq911 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq872
       grind)
    | exact superpose eq872 eq49
    | exact resolve eq49 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq872
  have eq916 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq911
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq911
    | exact resolve eq911 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq933 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq916 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq934 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq933
  have eq940 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq934
    | exact resolve eq934 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq1003 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq940 eq28
    | exact resolve eq28 eq940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq1006 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1003
       have r₂ := eq881
       grind)
    | exact resolve eq1003 eq881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881 eq1003
  have eq1008 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1006 eq30
    | exact resolve eq30 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1006
  have eq1033 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1008
    | exact resolve eq1008 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1008
  have eq1034 : x = y := by grind
  clear eq1033
  have eq1037 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1034
       grind)
    | exact superpose eq1034 eq19
    | exact resolve eq19 eq1034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1038 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1034
       grind)
    | exact superpose eq1034 eq25
    | exact resolve eq25 eq1034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1034
  have eq1056 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1038
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1038
    | exact resolve eq1038 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1038
  have eq1087 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1056 eq27
    | exact resolve eq27 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1056
  have eq1125 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1087 eq68
    | exact resolve eq68 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1087
  have eq1132 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1125
       have i₂ := eq1037
       grind)
    | exact superpose eq1037 eq1125
    | exact resolve eq1125 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037 eq1125
  have eq1136 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1132 eq15
    | exact resolve eq15 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132
  have eq1162 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1136
    | exact resolve eq1136 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1136
  have eq1167 : False := by grind
  exact eq1167

/-- `Equation3677`: `x ◇ x = (y ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else if m(X,X) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pyx_pxx_pxy_pyx_Equation3677 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3677 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3677.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  clear eq17
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq83 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq34 (τ X0)
       grind)
    | exact superpose eq34 eq18
    | exact resolve eq18 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq84 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq83
    | exact resolve eq83 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq84
    | exact resolve eq84 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq84
  have eq96 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq92 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq92
    | exact resolve eq92 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58 y x
       grind)
    | exact superpose eq58 eq16
    | (have j1 := eq58 y x
       grind)
    | exact resolve eq16 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq58 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq58 X0 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq58 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq58 X1 X1
       grind)
    | exact resolve eq13 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq58 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq58 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq58 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq58 X0 X1
       grind)
    | exact resolve eq12 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq58 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq141 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq137 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq142 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq138 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq138 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq138 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq138 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq138 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq143 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq141 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq141 X0 X0
       have r₂ := eq13 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq141 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq141 X1 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | exact resolve eq141 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq148 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq142 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq142
    | (have j0 := eq142 X0 X1
       grind)
    | exact resolve eq142 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq149 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq143 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq143
    | (have j0 := eq143 X0 X1
       grind)
    | exact resolve eq143 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq161 : ∀ X0 X1 : G, (M.op X1 (σ X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : ∀ X0 X1 : G, (M.op X1 (σ X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq466 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq134
       have i₂ := eq96 y
       grind)
    | exact superpose eq96 eq134
    | exact resolve eq134 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq467 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq466
       have i₂ := eq96 x
       grind)
    | exact superpose eq96 eq466
    | exact resolve eq466 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq468 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq467
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq467
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq467 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq469 : (M.op x x) = (M.op y x) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq468
  have eq1030 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 X1
       have i₂ := eq96 X1
       grind)
    | exact superpose eq96 eq148
    | (have j0 := eq148 X0 X1
       grind)
    | exact resolve eq148 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq1031 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1030 X0 X1
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq1030
    | (have j0 := eq1030 X0 X1
       grind)
    | exact resolve eq1030 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030
  have eq1032 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1031 X0 X1
       have i₂ := eq96 X1
       grind)
    | exact superpose eq96 eq1031
    | (have j0 := eq1031 X0 X1
       grind)
    | exact resolve eq1031 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031
  have eq1120 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq149 X0 X1
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq149
    | (have j0 := eq149 X0 X1
       grind)
    | exact resolve eq149 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq1121 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1120 X0 X1
       have i₂ := eq96 X1
       grind)
    | exact superpose eq96 eq1120
    | (have j0 := eq1120 X0 X1
       grind)
    | exact resolve eq1120 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1128 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1121 (τ X1) (τ X0)
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq1121
    | (have j0 := eq1121 (τ X0) (τ X1)
       grind)
    | exact resolve eq1121 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1161 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1128 X0 X1
       have i₂ := eq92 X0
       grind)
    | exact superpose eq92 eq1128
    | (have j0 := eq1128 X0 X1
       grind)
    | exact resolve eq1128 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128
  have eq1175 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1161 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1161
    | (have j0 := eq1161 X0 X1
       grind)
    | exact resolve eq1161 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161
  have eq1185 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1175 X0 X1
       have i₂ := eq92 X1
       grind)
    | exact superpose eq92 eq1175
    | (have j0 := eq1175 X0 X1
       grind)
    | exact resolve eq1175 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175
  have eq1192 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1185 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1185
    | (have j0 := eq1185 X0 X1
       grind)
    | exact resolve eq1185 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq1198 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1192 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1192
    | (have j0 := eq1192 X0 X1
       grind)
    | exact resolve eq1192 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192
  have eq1203 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1198 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1198
    | (have j0 := eq1198 X0 X1
       grind)
    | exact resolve eq1198 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq1208 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1203 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1203
    | (have j0 := eq1203 X0 X1
       grind)
    | exact resolve eq1203 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203
  have eq1209 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1208 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1208
    | (have j0 := eq1208 X0 X1
       grind)
    | exact resolve eq1208 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq1211 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq140 X0 X1
       have i₂ := eq96 X1
       grind)
    | exact superpose eq96 eq140
    | (have j0 := eq140 X0 X1
       grind)
    | exact resolve eq140 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq1212 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1211 X0 X1
       have i₂ := eq96 X1
       grind)
    | exact superpose eq96 eq1211
    | (have j0 := eq1211 X0 X1
       grind)
    | exact resolve eq1211 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq1213 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1212 X0 X1
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq1212
    | (have j0 := eq1212 X0 X1
       grind)
    | exact resolve eq1212 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq1220 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1213 (τ X1) (τ X0)
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq1213
    | (have j0 := eq1213 (τ X1) (τ X0)
       grind)
    | exact resolve eq1213 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1251 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1220 X0 X1
       have i₂ := eq92 X0
       grind)
    | exact superpose eq92 eq1220
    | (have j0 := eq1220 X0 X1
       grind)
    | exact resolve eq1220 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220
  have eq1263 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1251 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1251
    | (have j0 := eq1251 X0 X1
       grind)
    | exact resolve eq1251 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq1275 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1263 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1263
    | (have j0 := eq1263 X0 X1
       grind)
    | exact resolve eq1263 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263
  have eq1283 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1275 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1275
    | (have j0 := eq1275 X0 X1
       grind)
    | exact resolve eq1275 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275
  have eq1289 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1283 X0 X1
       have i₂ := eq92 X0
       grind)
    | exact superpose eq92 eq1283
    | (have j0 := eq1283 X0 X1
       grind)
    | exact resolve eq1283 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283
  have eq1294 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1289 X0 X1
       have i₂ := eq92 X1
       grind)
    | exact superpose eq92 eq1289
    | (have j0 := eq1289 X0 X1
       grind)
    | exact resolve eq1289 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq1289
  have eq1297 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1294 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1294
    | (have j0 := eq1294 X0 X1
       grind)
    | exact resolve eq1294 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294
  have eq1298 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1297 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1297
    | (have j0 := eq1297 X0 X1
       grind)
    | exact resolve eq1297 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297
  have eq6719 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op y y) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq469
       grind)
    | exact superpose eq469 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq469
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq469
       grind)
    | exact resolve eq12 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq6727 : (k y x) = (M.op y y) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq6719
  have eq249231 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1213 x y
       have i₂ := eq6727
       grind)
    | exact superpose eq6727 eq1213
    | (have j0 := eq1213 x y
       grind)
    | exact resolve eq1213 eq6727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6727
  have eq249383 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq249231
  have eq249384 : (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq249383
  have eq249413 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq162 x (σ y)
       have i₂ := eq249384
       grind)
    | exact superpose eq249384 eq162
    | (have j0 := eq162 x (σ y)
       grind)
    | (have r₁ := eq162 x (σ y)
       have r₂ := eq249384
       grind)
    | (have r₁ := eq162 y (σ x)
       have r₂ := eq249384
       grind)
    | exact resolve eq162 eq249384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249384
  have eq249495 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq249413
  have eq249560 : (σ (k y x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq249495
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq249495
    | exact resolve eq249495 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249495
  have eq249593 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq249560
       have i₂ := eq96 y
       grind)
    | exact superpose eq96 eq249560
    | exact resolve eq249560 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249560
  have eq249622 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq162 y (σ x)
       have i₂ := eq249593
       grind)
    | exact superpose eq249593 eq162
    | (have j0 := eq162 y (σ x)
       grind)
    | (have r₁ := eq162 y (σ x)
       have r₂ := eq249593
       grind)
    | exact resolve eq162 eq249593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249593
  have eq249699 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq249622
  have eq249759 : (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq249699
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq249699
    | exact resolve eq249699 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249699
  have eq249788 : (M.op x y) = (M.op y y) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq249759
       have i₂ := eq96 x
       grind)
    | exact superpose eq96 eq249759
    | exact resolve eq249759 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249759
  have eq250228 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (k x y)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq249788
       grind)
    | exact superpose eq249788 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq249788
       grind)
    | exact resolve eq12 eq249788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249788
  have eq1167269 : (M.op x x) = (k x y) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (k x y)) := by
    first
    | (have j0 := eq250228 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250228
  have eq1169026 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1032 x y
       have i₂ := eq1167269
       grind)
    | exact superpose eq1167269 eq1032
    | (have j0 := eq1032 x y
       grind)
    | (have r₁ := eq1032 y x
       have r₂ := eq1167269
       grind)
    | (have r₁ := eq1032 x y
       have r₂ := eq1167269
       grind)
    | exact resolve eq1032 eq1167269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1169032 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1213 y x
       have i₂ := eq1167269
       grind)
    | exact superpose eq1167269 eq1213
    | (have j0 := eq1213 y x
       grind)
    | (have r₁ := eq1213 x y
       have r₂ := eq1167269
       grind)
    | (have r₁ := eq1213 y x
       have r₂ := eq1167269
       grind)
    | exact resolve eq1213 eq1167269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167269
  have eq1169264 : (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (k x y)) := by grind
  clear eq1169032
  have eq1169270 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (k x y)) := by grind
  clear eq1169026
  have eq1169271 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (k x y)) := by grind
  clear eq1169270
  have eq1169320 : (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (k x y)) := by
    first
    | (have j1 := eq1213 y x
       grind)
    | (have r₁ := eq1169264
       have r₂ := eq1213 x y
       grind)
    | (have r₁ := eq1169264
       have r₂ := eq1213 y x
       grind)
    | exact resolve eq1169264 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169264
  have eq1169322 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have j1 := eq1032 x y
       grind)
    | (have r₁ := eq1169271
       have r₂ := eq1032 y x
       grind)
    | (have r₁ := eq1169271
       have r₂ := eq1032 x y
       grind)
    | exact resolve eq1169271 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032 eq1169271
  have eq1169374 : (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have j1 := eq1213 y x
       grind)
    | (have r₁ := eq1169320
       have r₂ := eq1213 y x
       grind)
    | exact resolve eq1169320 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213 eq1169320
  have eq1171341 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1169322
       grind)
    | exact superpose eq1169322 eq16
    | exact resolve eq16 eq1169322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1171377 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq161 y (σ x)
       have i₂ := eq1169322
       grind)
    | exact superpose eq1169322 eq161
    | (have j0 := eq161 y (σ x)
       grind)
    | (have r₁ := eq161 y (σ x)
       have r₂ := eq1169322
       grind)
    | exact resolve eq161 eq1169322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1171378 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq162 y (σ x)
       have i₂ := eq1169322
       grind)
    | exact superpose eq1169322 eq162
    | (have j0 := eq162 y (σ x)
       grind)
    | (have r₁ := eq162 y (σ x)
       have r₂ := eq1169322
       grind)
    | exact resolve eq162 eq1169322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169322
  have eq1171561 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ (k y x)) = (σ (M.op y y)) := by grind
  clear eq1171378
  have eq1171562 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op y y)) := by grind
  clear eq1171377
  have eq1171667 : (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1171561
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1171561
    | exact resolve eq1171561 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171561
  have eq1171668 : (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1171562
       have i₂ := eq96 x
       grind)
    | exact superpose eq96 eq1171562
    | exact resolve eq1171562 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171562
  have eq1171717 : (σ (k y x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1171667
       have i₂ := eq96 x
       grind)
    | exact superpose eq96 eq1171667
    | exact resolve eq1171667 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171667
  have eq1171718 : (σ (k y x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1171668
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1171668
    | exact resolve eq1171668 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171668
  have eq1171745 : (σ (k y x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq1121 y x
       grind)
    | (have r₁ := eq1171718
       have r₂ := eq1121 y x
       grind)
    | exact resolve eq1171718 eq1121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121 eq1171718
  have eq1172863 : (k y x) = (τ (σ (M.op y y))) ∨ (σ (M.op x x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq1171717
       grind)
    | exact superpose eq1171717 eq10
    | exact resolve eq10 eq1171717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1173672 : (k y x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1172863
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq1172863
    | exact resolve eq1172863 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172863
  have eq1175069 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x x) = (M.op y x) ∨ (σ (M.op x x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1298 y x
       have i₂ := eq1173672
       grind)
    | exact superpose eq1173672 eq1298
    | (have j0 := eq1298 y x
       grind)
    | (have r₁ := eq1298 y x
       have r₂ := eq1173672
       grind)
    | exact resolve eq1298 eq1173672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298 eq1173672
  have eq1175297 : (M.op x x) = (M.op y x) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x x)) = (σ (k x y)) := by grind
  clear eq1175069
  have eq1179759 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq161 x (σ y)
       have i₂ := eq1169374
       grind)
    | exact superpose eq1169374 eq161
    | (have j0 := eq161 x (σ y)
       grind)
    | (have r₁ := eq161 x (σ y)
       have r₂ := eq1169374
       grind)
    | (have r₁ := eq161 y (σ x)
       have r₂ := eq1169374
       grind)
    | exact resolve eq161 eq1169374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161 eq1169374
  have eq1179949 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq1179759
  have eq1180087 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1179949
       have i₂ := eq96 y
       grind)
    | exact superpose eq96 eq1179949
    | exact resolve eq1179949 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179949
  have eq1180088 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1180087
  have eq1180141 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1180088
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1180088
    | exact resolve eq1180088 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180088
  have eq1184765 : (σ (k y x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq162 x (σ y)
       have i₂ := eq1171745
       grind)
    | exact superpose eq1171745 eq162
    | (have j0 := eq162 x (σ y)
       grind)
    | (have r₁ := eq162 x (σ y)
       have r₂ := eq1171745
       grind)
    | exact resolve eq162 eq1171745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171745
  have eq1185184 : (σ (k y x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have j1 := eq162 x (σ y)
       grind)
    | (have r₁ := eq1184765
       have r₂ := eq162 x (σ y)
       grind)
    | exact resolve eq1184765 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184765
  have eq1185330 : (σ (k y x)) = (M.op (σ y) (σ y)) ∨ (σ (k y x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1185184
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1185184
    | exact resolve eq1185184 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185184
  have eq1185452 : (σ (k y x)) ≠ (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1185330
       have i₂ := eq96 y
       grind)
    | exact superpose eq96 eq1185330
    | exact resolve eq1185330 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185330
  have eq1189992 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1180141
       grind)
    | exact superpose eq1180141 eq16
    | exact resolve eq16 eq1180141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1190104 : (M.op (σ y) (σ y)) = (M.op (σ (k x y)) (σ (k x y))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 (σ y) (σ x)
       have i₂ := eq1180141
       grind)
    | exact superpose eq1180141 eq9
    | exact resolve eq9 eq1180141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180141
  have eq1190398 : (M.op (σ y) (σ y)) = (σ (M.op (k x y) (k x y))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1190104
       have i₂ := eq96 (k x y)
       grind)
    | exact superpose eq96 eq1190104
    | exact resolve eq1190104 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190104
  have eq1190539 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (M.op y y)) = (σ (M.op (k x y) (k x y))) := by
    first
    | (have i₁ := eq1190398
       have i₂ := eq96 y
       grind)
    | exact superpose eq96 eq1190398
    | exact resolve eq1190398 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190398
  have eq1220285 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (σ (M.op (k x y) (k x y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1190539
       grind)
    | exact superpose eq1190539 eq16
    | exact resolve eq16 eq1190539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1220324 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ (M.op y y)) = (σ (M.op (k x y) (k x y))) := by
    first
    | (have i₁ := eq162 y (σ x)
       have i₂ := eq1190539
       grind)
    | exact superpose eq1190539 eq162
    | (have j0 := eq162 y (σ x)
       grind)
    | (have r₁ := eq162 y (σ x)
       have r₂ := eq1190539
       grind)
    | exact resolve eq162 eq1190539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190539
  have eq1220507 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ (M.op y y)) = (σ (M.op (k x y) (k x y))) := by grind
  clear eq1220324
  have eq1220610 : (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (σ (M.op y y)) = (σ (M.op (k x y) (k x y))) := by
    first
    | (have i₁ := eq1220507
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1220507
    | exact resolve eq1220507 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220507
  have eq1220660 : (σ (M.op x x)) = (σ (k x y)) ∨ (σ (M.op y y)) = (σ (M.op (k x y) (k x y))) := by
    first
    | (have i₁ := eq1220610
       have i₂ := eq96 x
       grind)
    | exact superpose eq96 eq1220610
    | exact resolve eq1220610 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220610
  have eq1225062 : (σ (M.op (k x y) (k x y))) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ (σ (M.op y y)) = (σ (M.op (k x y) (k x y))) := by
    first
    | (have i₁ := eq96 (k x y)
       have i₂ := eq1220660
       grind)
    | exact superpose eq1220660 eq96
    | exact resolve eq96 eq1220660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220660
  have eq1225850 : (σ (M.op (k x y) (k x y))) = (σ (M.op (M.op x x) (M.op x x))) ∨ (σ (M.op y y)) = (σ (M.op (k x y) (k x y))) := by
    first
    | (have i₁ := eq1225062
       have i₂ := eq96 (M.op x x)
       grind)
    | exact superpose eq96 eq1225062
    | exact resolve eq1225062 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225062
  have eq1225868 : (σ (M.op y y)) = (σ (M.op (k x y) (k x y))) ∨ (σ (M.op x x)) = (σ (M.op (k x y) (k x y))) := by
    first
    | (have i₁ := eq1225850
       have i₂ := eq9 x x
       grind)
    | exact superpose eq9 eq1225850
    | exact resolve eq1225850 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225850
  have eq1230908 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1175297
       grind)
    | exact superpose eq1175297 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1175297
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1175297
       grind)
    | exact resolve eq13 eq1175297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175297
  have eq1230999 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k x y) ∨ (σ (M.op x x)) = (σ (k x y)) := by grind
  clear eq1230908
  have eq1231000 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x x)) = (σ (k x y)) := by grind
  clear eq1230999
  have eq1243130 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1189992
       have i₂ := eq1231000
       grind)
    | exact superpose eq1231000 eq1189992
    | exact resolve eq1189992 eq1231000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231000
  have eq1243545 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x x)) = (σ (k x y)) := by grind
  clear eq1243130
  have eq1863265 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq162 y (σ x)
       have i₂ := eq1243545
       grind)
    | exact superpose eq1243545 eq162
    | (have j0 := eq162 y (σ x)
       grind)
    | (have r₁ := eq162 y (σ x)
       have r₂ := eq1243545
       grind)
    | exact resolve eq162 eq1243545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq1243545
  have eq1863448 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x x)) = (σ (k x y)) := by grind
  clear eq1863265
  have eq1863552 : (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1863448
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1863448
    | exact resolve eq1863448 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1863448
  have eq1863602 : (σ (M.op x x)) = (σ (k x y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1863552
       have i₂ := eq96 x
       grind)
    | exact superpose eq96 eq1863552
    | exact resolve eq1863552 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq1863552
  have eq1863603 : (M.op x y) = (M.op y y) ∨ (σ (M.op x x)) = (σ (k x y)) := by grind
  clear eq1863602
  have eq1867940 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (k y x)) ∨ (σ (M.op x x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1171341
       have i₂ := eq1863603
       grind)
    | exact superpose eq1863603 eq1171341
    | exact resolve eq1171341 eq1863603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1863603
  have eq1868182 : (σ (M.op x y)) = (σ (k y x)) ∨ (σ (M.op x x)) = (σ (k x y)) := by grind
  clear eq1867940
  have eq1871107 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (k x y)) ∨ (σ (M.op x x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1171717
       have i₂ := eq1868182
       grind)
    | exact superpose eq1868182 eq1171717
    | exact resolve eq1171717 eq1868182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171717 eq1868182
  have eq1871848 : (σ (M.op x x)) = (σ (k x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq1871107
  have eq1876645 : (k x y) = (τ (σ (M.op x x))) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq1871848
       grind)
    | exact superpose eq1871848 eq10
    | exact resolve eq10 eq1871848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1871848
  have eq1877490 : (M.op x x) = (k x y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1876645
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq1876645
    | exact resolve eq1876645 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1876645
  have eq1877548 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1209 x y
       have i₂ := eq1877490
       grind)
    | exact superpose eq1877490 eq1209
    | (have j0 := eq1209 x y
       grind)
    | (have r₁ := eq1209 x y
       have r₂ := eq1877490
       grind)
    | exact resolve eq1209 eq1877490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209 eq1877490
  have eq1877816 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq1877548
  have eq2048580 : (M.op y y) = (M.op (M.op x x) (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq1877816
       grind)
    | exact superpose eq1877816 eq9
    | exact resolve eq9 eq1877816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2048737 : (M.op y y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2048580
       have i₂ := eq9 x x
       grind)
    | exact superpose eq9 eq2048580
    | exact resolve eq2048580 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048580
  have eq2052646 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq2048737
  have eq2052650 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq2052646
       have r₂ := eq1877816
       grind)
    | exact resolve eq2052646 eq1877816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877816 eq2052646
  have eq2052659 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1171341
       have i₂ := eq2052650
       grind)
    | exact superpose eq2052650 eq1171341
    | (have r₁ := eq1171341
       have r₂ := eq2052650
       grind)
    | exact resolve eq1171341 eq2052650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171341
  have eq2052660 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op (k x y) (k x y))) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1220285
       have i₂ := eq2052650
       grind)
    | exact superpose eq2052650 eq1220285
    | (have r₁ := eq1220285
       have r₂ := eq2052650
       grind)
    | exact resolve eq1220285 eq2052650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052650
  have eq2052917 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op (k x y) (k x y))) := by grind
  clear eq2052660
  have eq2052918 : (σ (M.op x y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq2052659
  have eq2052943 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1185452
       have i₂ := eq2052918
       grind)
    | exact superpose eq2052918 eq1185452
    | exact resolve eq1185452 eq2052918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185452 eq2052918
  have eq2053723 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq2052943
  have eq2102489 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op (k x y) (k x y))) ∨ (σ (M.op x y)) = (σ (M.op (k x y) (k x y))) := by
    first
    | (have i₁ := eq1220285
       have i₂ := eq2052917
       grind)
    | exact superpose eq2052917 eq1220285
    | (have r₁ := eq1220285
       have r₂ := eq2052917
       grind)
    | exact resolve eq1220285 eq2052917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220285 eq2052917
  have eq2103331 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op (k x y) (k x y))) := by grind
  clear eq2102489
  have eq2103332 : (σ (M.op x y)) = (σ (M.op (k x y) (k x y))) := by grind
  clear eq2103331
  have eq2103996 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1225868
       have i₂ := eq2103332
       grind)
    | exact superpose eq2103332 eq1225868
    | exact resolve eq1225868 eq2103332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225868
  have eq2104162 : (M.op (k x y) (k x y)) = (τ (σ (M.op x y))) := by
    first
    | (have i₁ := eq10 (M.op (k x y) (k x y))
       have i₂ := eq2103332
       grind)
    | exact superpose eq2103332 eq10
    | exact resolve eq10 eq2103332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2103332
  have eq2105468 : (M.op x y) = (M.op (k x y) (k x y)) := by
    first
    | (have i₁ := eq2104162
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq2104162
    | exact resolve eq2104162 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2104162
  have eq2105469 : (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq2103996
       have r₂ := eq2053723
       grind)
    | exact resolve eq2103996 eq2053723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2053723 eq2103996
  have eq2106952 : (M.op y y) = (τ (σ (M.op x y))) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2105469
       grind)
    | exact superpose eq2105469 eq10
    | exact resolve eq10 eq2105469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2108230 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2106952
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq2106952
    | exact resolve eq2106952 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2106952
  have eq2108694 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq2108230
       grind)
    | exact superpose eq2108230 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq2108230
       grind)
    | exact resolve eq12 eq2108230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2108230
  have eq2117932 : (M.op x x) = (k x y) := by
    first
    | (have j0 := eq2108694 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2108694
  have eq2120766 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1189992
       have i₂ := eq2117932
       grind)
    | exact superpose eq2117932 eq1189992
    | exact resolve eq1189992 eq2117932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189992
  have eq2120805 : (M.op x y) = (M.op (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq2105468
       have i₂ := eq2117932
       grind)
    | exact superpose eq2117932 eq2105468
    | exact resolve eq2105468 eq2117932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2105468 eq2117932
  have eq2121134 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2120805
       have i₂ := eq9 x x
       grind)
    | exact superpose eq9 eq2120805
    | exact resolve eq2120805 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2120805
  have eq2121147 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2120766
       have i₂ := eq2105469
       grind)
    | exact superpose eq2105469 eq2120766
    | exact resolve eq2120766 eq2105469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2105469 eq2120766
  have eq2121163 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have r₁ := eq2121147
       have r₂ := eq16
       grind)
    | exact resolve eq2121147 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2121147
  have eq2126172 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2121163
       have i₂ := eq2121134
       grind)
    | exact superpose eq2121134 eq2121163
    | exact resolve eq2121163 eq2121134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2121134 eq2121163
  have eq2126173 : False := by grind
  exact eq2126173

/-- `Equation3677`: `x ◇ x = (y ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_x_pxx_x_pyx_Equation3677 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3677 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3677.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq28 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq34 (σ X0)
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq34 (τ X0)
       grind)
    | exact superpose eq34 eq18
    | exact resolve eq18 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq40
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq43 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq38
    | exact resolve eq38 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq45 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq41
    | exact resolve eq41 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq80 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq86 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq29
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 (τ X1)) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq101 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq10
    | exact resolve eq10 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq91 X0 (k X1 (τ X0))
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq91
    | exact resolve eq91 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq91 x y
       grind)
    | exact superpose eq91 eq16
    | (have j1 := eq91 x y
       grind)
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (k X0 X1)) (σ (k X0 X1))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq9
    | (have j1 := eq91 X1 X0
       grind)
    | exact resolve eq9 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq190 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op (k X0 X1) (k X0 X1))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq185 X0 X1
       have i₂ := eq43 (k X0 X1)
       grind)
    | exact superpose eq43 eq185
    | (have j0 := eq185 X0 X1
       grind)
    | exact resolve eq185 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq194 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq176
    | (have j0 := eq176 X0 X1
       grind)
    | exact resolve eq176 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq199 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op (k X0 X1) (k X0 X1))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq190 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq190
    | (have j0 := eq190 X0 X1
       grind)
    | exact resolve eq190 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq532 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (σ X0)
       have i₂ := eq194 (σ X1) X0
       grind)
    | exact superpose eq194 eq29
    | (have j1 := eq194 (σ X1) X0
       grind)
    | exact resolve eq29 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq532 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq532
    | (have j0 := eq532 X0 X1
       grind)
    | exact resolve eq532 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq597 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq87
    | exact resolve eq87 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq637 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq597 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq597
    | (have j0 := eq597 X0 X1
       grind)
    | exact resolve eq597 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq2568 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (k (σ X0) X1) ∨ (k (σ X0) X1) = (k (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k (σ X0) X1) (σ X2)
       have i₂ := eq178 X0 X1 X2
       grind)
    | exact superpose eq178 eq13
    | (have j0 := eq13 (k (σ X0) X1) (σ X2)
       have j1 := eq178 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq178 X0 X1 X2
       grind)
    | exact resolve eq13 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2570 : ∀ X0 X1 X2 : G, (k (σ X1) X2) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (k (σ X1) X2)) ∨ (M.op (σ X0) (k (σ X1) X2)) = (σ (k (k X1 (τ X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq178 X1 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2571 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (k (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2568 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2568
  have eq2573 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (k (k X0 (τ X1)) X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2571 X0 X1 X2
       have i₂ := eq28 X0 X1 X2
       grind)
    | exact superpose eq28 eq2571
    | (have j0 := eq2571 X0 X1 X2
       grind)
    | exact resolve eq2571 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2571
  have eq2619 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (M.op X2 X2)) ∨ (k (σ X0) X1) = (σ (k (k X0 (τ X1)) X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2573 X0 X1 X2
       have i₂ := eq43 X2
       grind)
    | exact superpose eq43 eq2573
    | (have j0 := eq2573 X0 X1 X2
       grind)
    | exact resolve eq2573 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2573
  have eq2644 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (k (k X0 (τ X1)) X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2619 X0 X1 X2
       have j1 := eq2570 X2 X0 X1
       grind)
    | (have r₁ := eq2619 X1 X2 X0
       have r₂ := eq2570 X0 X1 X2
       grind)
    | exact resolve eq2619 eq2570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2570 eq2619
  have eq4732 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq637 X0 X1
       grind)
    | exact superpose eq637 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq637 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq637 X0 X1
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq637 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4733 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq637 X0 X1
       grind)
    | exact superpose eq637 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq637 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq637 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq637 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq637 X0 X0
       grind)
    | exact resolve eq12 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4744 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq637 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq4745 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq4732 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4732
  have eq4754 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4733 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq4733 (k X0 X1) X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq4733 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq4733 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq4733 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4733
  have eq4755 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq4745 X0 X1
       have j1 := eq4744 X1 X0
       grind)
    | (have r₁ := eq4745 (M.op X0 X0) X1
       have r₂ := eq4744 X0 (k (M.op X0 X0) X1)
       grind)
    | (have r₁ := eq4745 X1 X0
       have r₂ := eq4744 X0 X1
       grind)
    | (have r₁ := eq4745 (M.op X0 X0) X1
       have r₂ := eq4744 X0 (M.op X1 X1)
       grind)
    | exact resolve eq4745 eq4744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4744 eq4745
  have eq5343 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (σ (k (M.op X0 X0) X0)) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq4754 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4754
  have eq5344 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (σ (k (M.op X0 X0) X0)) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq5343 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq5343
    | (have j0 := eq5343 X0
       grind)
    | exact resolve eq5343 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5343
  have eq5419 : ∀ X0 X1 : G, (τ X1) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq4755 (τ X1) X0
       grind)
    | exact superpose eq4755 eq17
    | (have j1 := eq4755 (τ X1) X0
       grind)
    | exact resolve eq17 eq4755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5430 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq4755 X1 X0
       grind)
    | exact superpose eq4755 eq10
    | (have j1 := eq4755 X1 X0
       grind)
    | exact resolve eq10 eq4755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4755
  have eq5484 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5430 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq5430
    | (have j0 := eq5430 X0 X1
       grind)
    | exact resolve eq5430 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5430
  have eq5517 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5484 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5484
    | (have j0 := eq5484 (σ X1) (σ X0)
       grind)
    | exact resolve eq5484 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5541 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (k X1 (σ X0)) = X1 ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X0
       have i₂ := eq5484 (σ X0) X1
       grind)
    | exact superpose eq5484 eq23
    | (have j1 := eq5484 (σ X0) X1
       grind)
    | exact resolve eq23 eq5484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5484
  have eq5687 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5541 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq5541
    | (have j0 := eq5541 X0 X1
       grind)
    | exact resolve eq5541 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5541
  have eq5701 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5517 X0 X1
       have i₂ := eq43 X1
       grind)
    | exact superpose eq43 eq5517
    | (have j0 := eq5517 X0 X1
       grind)
    | exact resolve eq5517 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5517
  have eq6058 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (σ (k (M.op (τ X0) (τ X0)) (τ X0))) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq5344 (τ X0)
       grind)
    | exact superpose eq5344 eq18
    | (have j1 := eq5344 (τ X0)
       grind)
    | exact resolve eq18 eq5344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5344
  have eq6111 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (σ (k (M.op (τ X0) (τ X0)) (τ X0))) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq6058 X0
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq6058
    | (have j0 := eq6058 X0
       grind)
    | exact resolve eq6058 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6058
  have eq6137 : ∀ X0 : G, (σ (k (τ (M.op X0 X0)) (τ X0))) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq6111 X0
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq6111
    | (have j0 := eq6111 X0
       grind)
    | exact resolve eq6111 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6111
  have eq6163 : ∀ X0 : G, (σ (M.op (τ X0) (τ (M.op X0 X0)))) = (k (σ (τ (M.op X0 X0))) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq6137 X0
       have i₂ := eq18 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq18 eq6137
    | (have j0 := eq6137 X0
       grind)
    | exact resolve eq6137 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6137
  have eq6188 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq6163 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq6163
    | (have j0 := eq6163 X0
       grind)
    | exact resolve eq6163 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6163
  have eq6244 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq86
    | exact resolve eq86 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq6311 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6244 X0 X1
       have i₂ := eq47 X1 X0
       grind)
    | exact superpose eq47 eq6244
    | (have j0 := eq6244 X0 X1
       grind)
    | exact resolve eq6244 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6244
  have eq6343 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq6311 X0 X1
       grind)
    | exact superpose eq6311 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq6311 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq6311 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq6311 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq6311 X0 X0
       grind)
    | exact resolve eq12 eq6311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6368 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq6311 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6311
  have eq6387 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq6343 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq6343 (k X0 X1) X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq6343 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq6343 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq6343 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6343
  have eq6404 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (τ (M.op X0 (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq6368 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6368
  have eq6697 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (τ (M.op X0 (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq6387 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6387
  have eq6698 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (τ (M.op X0 (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq6697 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq6697
    | (have j0 := eq6697 X0
       grind)
    | exact resolve eq6697 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6697
  have eq6912 : ∀ X0 : G, (M.op (σ X0) (σ X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) = (k (M.op (σ X0) (σ X0)) (σ X0)) ∨ (τ (k (M.op (σ X0) (σ X0)) (σ X0))) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq80 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq6404 (σ X0)
       grind)
    | exact superpose eq6404 eq80
    | (have j0 := eq80 X0 (σ X0)
       have j1 := eq6404 (σ X0)
       grind)
    | exact resolve eq80 eq6404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6404
  have eq6929 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) = (k (M.op (σ X0) (σ X0)) (σ X0)) ∨ (τ (k (M.op (σ X0) (σ X0)) (σ X0))) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have j0 := eq6912 X0
       grind)
    | (have r₁ := eq6912 X0
       have r₂ := eq43 X0
       grind)
    | exact resolve eq6912 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6912
  have eq6941 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (τ (k (M.op (σ X0) (σ X0)) (σ X0))) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq6929 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq6929
    | (have j0 := eq6929 X0
       grind)
    | exact resolve eq6929 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6929
  have eq6948 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) ∨ (τ (k (M.op (σ X0) (σ X0)) (σ X0))) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq6941 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq6941
    | (have j0 := eq6941 X0
       grind)
    | exact resolve eq6941 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6941
  have eq6954 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) ∨ (τ (k (M.op (σ X0) (σ X0)) (σ X0))) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq6948 X0
       have i₂ := eq43 (M.op X0 X0)
       grind)
    | exact superpose eq43 eq6948
    | (have j0 := eq6948 X0
       grind)
    | exact resolve eq6948 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6948
  have eq6960 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) ∨ (τ (k (M.op (σ X0) (σ X0)) (σ X0))) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq6954 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq6954
    | (have j0 := eq6954 X0
       grind)
    | exact resolve eq6954 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6954
  have eq6966 : ∀ X0 : G, (τ (k (σ (M.op X0 X0)) (σ X0))) = (τ (M.op (σ X0) (σ (M.op X0 X0)))) ∨ (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq6960 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq6960
    | (have j0 := eq6960 X0
       grind)
    | exact resolve eq6960 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6960
  have eq6971 : ∀ X0 : G, (k (τ (σ (M.op X0 X0))) X0) = (τ (M.op (σ X0) (σ (M.op X0 X0)))) ∨ (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq6966 X0
       have i₂ := eq23 (σ (M.op X0 X0)) X0
       grind)
    | exact superpose eq23 eq6966
    | (have j0 := eq6966 X0
       grind)
    | exact resolve eq6966 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6966
  have eq6976 : ∀ X0 : G, (k (M.op X0 X0) X0) = (τ (M.op (σ X0) (σ (M.op X0 X0)))) ∨ (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq6971 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq6971
    | (have j0 := eq6971 X0
       grind)
    | exact resolve eq6971 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6971
  have eq7067 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) ∨ (τ (k (M.op (σ X0) (σ X0)) (σ X0))) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq6698 (σ X0)
       grind)
    | exact superpose eq6698 eq23
    | (have j1 := eq6698 (σ X0)
       grind)
    | exact resolve eq23 eq6698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6698
  have eq7132 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (k (τ (σ (M.op X0 X0))) X0) ∨ (τ (k (M.op (σ X0) (σ X0)) (σ X0))) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq7067 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq7067
    | (have j0 := eq7067 X0
       grind)
    | exact resolve eq7067 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7067
  have eq7160 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (τ (k (M.op (σ X0) (σ X0)) (σ X0))) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq7132 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq7132
    | (have j0 := eq7132 X0
       grind)
    | exact resolve eq7132 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7132
  have eq7188 : ∀ X0 : G, (τ (k (σ (M.op X0 X0)) (σ X0))) = (τ (M.op (σ X0) (σ (M.op X0 X0)))) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq7160 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq7160
    | (have j0 := eq7160 X0
       grind)
    | exact resolve eq7160 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7160
  have eq7212 : ∀ X0 : G, (k (τ (σ (M.op X0 X0))) X0) = (τ (M.op (σ X0) (σ (M.op X0 X0)))) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq7188 X0
       have i₂ := eq23 (σ (M.op X0 X0)) X0
       grind)
    | exact superpose eq23 eq7188
    | (have j0 := eq7188 X0
       grind)
    | exact resolve eq7188 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7188
  have eq7231 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (k (M.op X0 X0) X0) = (τ (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq7212 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq7212
    | (have j0 := eq7212 X0
       grind)
    | exact resolve eq7212 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7212
  have eq7967 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (M.op (σ X0) (σ X0))) ∨ (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op (τ (σ X0)) (τ (M.op (σ X0) (σ X0))))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ X0) (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq6188 (σ x)
       have i₂ := eq194 (M.op (σ x) (σ x)) x
       grind)
    | exact superpose eq194 eq6188
    | (have j1 := eq194 (M.op (σ X0) (σ X0)) X0
       grind)
    | exact resolve eq6188 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq6188
  have eq8025 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (M.op (σ X0) (σ X0))) ∨ (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op (τ (σ X0)) (τ (M.op (σ X0) (σ X0))))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq7967 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7967
  have eq8060 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op (τ (σ X0)) (τ (M.op (σ X0) (σ X0))))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq8025 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq8025
    | (have j0 := eq8025 X0
       grind)
    | exact resolve eq8025 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8025
  have eq8092 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (τ (σ X0)) (τ (σ (M.op X0 X0))))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq8060 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq8060
    | (have j0 := eq8060 X0
       grind)
    | exact resolve eq8060 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8060
  have eq8122 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (τ (σ X0)) (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq8092 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq8092
    | (have j0 := eq8092 X0
       grind)
    | exact resolve eq8092 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8092
  have eq8148 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq8122 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8122
    | (have j0 := eq8122 X0
       grind)
    | exact resolve eq8122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8122
  have eq8170 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq8148 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq8148
    | (have j0 := eq8148 X0
       grind)
    | exact resolve eq8148 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8148
  have eq8171 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq8170 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8170
  have eq8436 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = (τ (M.op (σ X0) (σ (M.op X0 X0)))) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7231 x
       have i₂ := eq14 (M.op x x) x
       grind)
    | exact superpose eq14 eq7231
    | (have j1 := eq14 (M.op X0 X0) X0
       grind)
    | exact resolve eq7231 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7231
  have eq8498 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = (τ (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq8436 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8436
  have eq9867 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) ∨ (M.op (τ X0) (τ (M.op X0 X0))) = (τ (M.op (σ (τ X0)) (σ (τ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq8498 (τ X0)
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq8498
    | exact resolve eq8498 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8498
  have eq9923 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (M.op (σ (τ X0)) (M.op X0 X0))) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9867 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq9867
    | (have j0 := eq9867 X0
       grind)
    | exact resolve eq9867 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9867
  have eq9950 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) ∨ (M.op (τ X0) (τ (M.op X0 X0))) = (τ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9923 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9923
    | (have j0 := eq9923 X0
       grind)
    | exact resolve eq9923 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9923
  have eq37375 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq5419 X1 X0
       grind)
    | exact superpose eq5419 eq17
    | (have j1 := eq5419 X1 X0
       grind)
    | exact resolve eq17 eq5419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5419
  have eq37622 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (k X0 (σ X1)) = X0 ∨ (M.op X1 X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq37375 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37375
    | (have j0 := eq37375 X0 X1
       grind)
    | exact resolve eq37375 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37375
  have eq37773 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37622 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq37622
    | (have j0 := eq37622 (σ X0) X1
       grind)
    | exact resolve eq37622 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37622
  have eq38012 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37773 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq37773
    | (have j0 := eq37773 X0 X1
       grind)
    | exact resolve eq37773 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37773
  have eq38064 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38012 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq38012
    | (have j0 := eq38012 X0 X1
       grind)
    | exact resolve eq38012 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38012
  have eq39762 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq180
       have i₂ := eq38064 y x
       grind)
    | exact superpose eq38064 eq180
    | (have j1 := eq38064 y x
       grind)
    | (have r₁ := eq180
       have r₂ := eq38064 y x
       grind)
    | exact resolve eq180 eq38064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq39888 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38064 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39889 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq39762
  have eq39963 : (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq189 x y
       grind)
    | (have r₁ := eq39889
       have r₂ := eq189 x y
       grind)
    | exact resolve eq39889 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq39889
  have eq46444 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) X0)
       have i₂ := eq5687 X1 X0
       grind)
    | exact superpose eq5687 eq11
    | (have j1 := eq5687 X1 X0
       grind)
    | exact resolve eq11 eq5687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5687
  have eq46595 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq46444 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq46444
    | (have j0 := eq46444 X0 X1
       grind)
    | exact resolve eq46444 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46444
  have eq46919 : ∀ X0 X1 : G, (M.op (σ X1) X0) ≠ X0 ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq46595 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46595
  have eq49243 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2644 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2644
  have eq49245 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq49243 X0 X1 X2
       have j1 := eq178 X0 X1 X2
       grind)
    | (have r₁ := eq49243 X0 X1 X2
       have r₂ := eq178 X0 X1 X2
       grind)
    | exact resolve eq49243 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq49243
  have eq60878 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ (M.op X0 X0)))
       have i₂ := eq6976 X0
       grind)
    | exact superpose eq6976 eq11
    | (have j1 := eq6976 X0
       grind)
    | exact resolve eq11 eq6976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6976
  have eq72434 : (M.op y y) = (M.op (M.op x x) (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq39963
       grind)
    | exact superpose eq39963 eq9
    | exact resolve eq9 eq39963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72435 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq39963
       grind)
    | exact superpose eq39963 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq39963
       grind)
    | exact resolve eq12 eq39963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39963
  have eq72452 : (k y x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq72435
  have eq72454 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq72434
       have i₂ := eq9 x x
       grind)
    | exact superpose eq9 eq72434
    | exact resolve eq72434 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72434
  have eq72877 : ∀ X0 : G, (σ (k (M.op (τ X0) (τ X0)) (τ X0))) = (M.op (σ (τ X0)) (M.op X0 X0)) ∨ (M.op X0 X0) = (σ (k (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60878 (τ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq60878
    | exact resolve eq60878 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60878
  have eq73104 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (k (M.op (τ X0) (τ X0)) (τ X0))) ∨ (M.op X0 X0) = (σ (k (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq72877 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq72877
    | (have j0 := eq72877 X0
       grind)
    | exact resolve eq72877 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72877
  have eq73179 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = (σ (k (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq73104 X0
       have i₂ := eq18 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq18 eq73104
    | (have j0 := eq73104 X0
       grind)
    | exact resolve eq73104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73104
  have eq73234 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (σ (k (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq73179 X0
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq73179
    | (have j0 := eq73179 X0
       grind)
    | exact resolve eq73179 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73179
  have eq73268 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73234 X0
       have i₂ := eq18 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq18 eq73234
    | (have j0 := eq73234 X0
       grind)
    | exact resolve eq73234 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73234
  have eq73300 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq73268 X0
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq73268
    | (have j0 := eq73268 X0
       grind)
    | exact resolve eq73268 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73268
  have eq73393 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) (τ X0)) ∨ (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq73300 (τ X0)
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq73300
    | exact resolve eq73300 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73300
  have eq73650 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) ∨ (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq73393 X0
       have i₂ := eq47 X0 (M.op X0 X0)
       grind)
    | exact superpose eq47 eq73393
    | (have j0 := eq73393 X0
       grind)
    | exact resolve eq73393 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73393
  have eq73722 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) ∨ (τ (M.op X0 X0)) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq73650 X0
       have i₂ := eq47 X0 (M.op X0 X0)
       grind)
    | exact superpose eq47 eq73650
    | (have j0 := eq73650 X0
       grind)
    | exact resolve eq73650 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73650
  have eq84926 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq188 x y
       have i₂ := eq72452
       grind)
    | exact superpose eq72452 eq188
    | (have j0 := eq188 x y
       grind)
    | exact resolve eq188 eq72452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq72452
  have eq84995 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq84926
  have eq84998 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq72454
       grind)
    | exact superpose eq72454 eq16
    | exact resolve eq16 eq72454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72454
  have eq117373 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (M.op X0 (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 (M.op X0 X0))) ∨ (k (M.op X0 X0) X0) = (τ (σ (M.op X0 (M.op X0 X0)))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq540 X0 (M.op X0 X0)
       have i₂ := eq8171 X0
       grind)
    | exact superpose eq8171 eq540
    | (have j0 := eq540 X0 (M.op X0 X0)
       have j1 := eq8171 X0
       grind)
    | exact resolve eq540 eq8171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq117458 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq8171 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8171
  have eq117477 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (M.op X0 (M.op X0 X0))) ∨ (k (M.op X0 X0) X0) = (τ (σ (M.op X0 (M.op X0 X0)))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq117373 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117373
  have eq117557 : ∀ X0 : G, (k (M.op X0 X0) X0) = (τ (σ (M.op X0 (M.op X0 X0)))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq117477 X0
       have j1 := eq117458 X0
       grind)
    | (have r₁ := eq117477 X0
       have r₂ := eq117458 X0
       grind)
    | exact resolve eq117477 eq117458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117458 eq117477
  have eq117654 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq117557 X0
       have i₂ := eq10 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq10 eq117557
    | (have j0 := eq117557 X0
       grind)
    | exact resolve eq117557 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117557
  have eq118740 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ (τ X0)) (M.op X0 X0)) ∨ (M.op (τ X0) (M.op (τ X0) (τ X0))) = (k (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq117654 (τ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq117654
    | (have j0 := eq117654 (τ X0)
       grind)
    | exact resolve eq117654 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117654
  have eq118851 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op (τ X0) (M.op (τ X0) (τ X0))) = (k (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq118740 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq118740
    | (have j0 := eq118740 X0
       grind)
    | exact resolve eq118740 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118740
  have eq118909 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) (τ X0)) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq118851 X0
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq118851
    | (have j0 := eq118851 X0
       grind)
    | exact resolve eq118851 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq118851
  have eq118945 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq118909 X0
       have i₂ := eq47 X0 (M.op X0 X0)
       grind)
    | exact superpose eq47 eq118909
    | (have j0 := eq118909 X0
       grind)
    | exact resolve eq118909 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq118909
  have eq132132 : ∀ X0 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 (M.op X0 X0))) ∨ (M.op (τ X0) (τ (M.op X0 X0))) = (τ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq9950 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9950
  have eq133773 : ∀ X0 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) ∨ (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq132132 X0
       have i₂ := eq118945 X0
       grind)
    | exact superpose eq118945 eq132132
    | (have j1 := eq118945 X0
       grind)
    | exact resolve eq132132 eq118945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118945 eq132132
  have eq133803 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) ∨ (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq133773 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133773
  have eq174618 : ∀ X0 : G, (τ (M.op X0 X0)) ≠ (τ (k (M.op X0 X0) X0)) ∨ (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq133803 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133803
  have eq174624 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq174618 X0
       have j1 := eq73722 X0
       grind)
    | (have r₁ := eq174618 X0
       have r₂ := eq73722 X0
       grind)
    | exact resolve eq174618 eq73722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73722 eq174618
  have eq175378 : ∀ X0 : G, (τ (k (σ (M.op X0 X0)) (σ X0))) = (M.op (τ (σ X0)) (τ (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq174624 (σ X0)
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq174624
    | exact resolve eq174624 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174624
  have eq175704 : ∀ X0 : G, (τ (k (σ (M.op X0 X0)) (σ X0))) = (M.op (τ (σ X0)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq175378 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq175378
    | exact resolve eq175378 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175378
  have eq175827 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (τ (k (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq175704 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq175704
    | exact resolve eq175704 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175704
  have eq175913 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (τ (σ (M.op X0 X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq175827 X0
       have i₂ := eq23 (σ (M.op X0 X0)) X0
       grind)
    | exact superpose eq23 eq175827
    | exact resolve eq175827 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175827
  have eq175987 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq175913 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq175913
    | exact resolve eq175913 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175913
  have eq176183 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq175987 (σ X0)
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq175987
    | exact resolve eq175987 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176609 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq176183 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq176183
    | exact resolve eq176183 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176183
  have eq176730 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq176609 X0
       have i₂ := eq175987 X0
       grind)
    | exact superpose eq175987 eq176609
    | exact resolve eq176609 eq175987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175987 eq176609
  have eq202800 : ∀ X0 X1 X2 : G, (k (σ (k X1 (τ X2))) X0) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (k X1 (τ X2))
       have i₂ := eq49245 X1 X2 (τ X0)
       grind)
    | exact superpose eq49245 eq18
    | (have j1 := eq49245 X1 X2 (τ X0)
       grind)
    | exact resolve eq18 eq49245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49245
  have eq203153 : ∀ X0 X1 X2 : G, (k (σ (k X1 (τ X2))) X0) = (M.op X0 (k (σ X1) X2)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq202800 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq202800
    | (have j0 := eq202800 X0 X1 X2
       grind)
    | exact resolve eq202800 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202800
  have eq203307 : ∀ X0 X1 X2 : G, (k (k (σ X1) X2) X0) = (M.op X0 (k (σ X1) X2)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq203153 X0 X1 X2
       have i₂ := eq18 X2 X1
       grind)
    | exact superpose eq18 eq203153
    | (have j0 := eq203153 X0 X1 X2
       grind)
    | exact resolve eq203153 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203153
  have eq203414 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) (τ X0))) = (M.op X0 (k (σ X1) X2)) ∨ (k (k (σ X1) X2) X0) = (M.op X0 (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq203307 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq203307
    | (have j0 := eq203307 X0 X1 X2
       grind)
    | exact resolve eq203307 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203307
  have eq203497 : ∀ X0 X1 X2 : G, (k (k (σ X1) X2) X0) = (M.op X0 (k (σ X1) X2)) ∨ (M.op X0 X0) = (M.op X0 (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq203414 X0 X1 X2
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq203414
    | (have j0 := eq203414 X0 X1 X2
       grind)
    | exact resolve eq203414 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq203414
  have eq220196 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (M.op X2 (k X0 X1)) ∨ (M.op X2 X2) = (M.op X2 (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq203497 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq203497
    | exact resolve eq203497 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203497
  have eq894337 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq5701 X0 X1
       grind)
    | exact superpose eq5701 eq10
    | (have j1 := eq5701 X0 X1
       grind)
    | exact resolve eq10 eq5701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5701
  have eq894856 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq894337 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq894337
    | (have j0 := eq894337 X0 X1
       grind)
    | exact resolve eq894337 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894337
  have eq899461 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq894856 y x
       grind)
    | exact superpose eq894856 eq16
    | (have j1 := eq894856 y x
       grind)
    | exact resolve eq16 eq894856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq900399 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (k X1 X0) = X1 ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq894856 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894856
  have eq916038 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq899461
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq899461
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq899461 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899461
  have eq916047 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq916038
  have eq916048 : y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq916047
  have eq918992 : (σ y) ≠ (σ y) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq84998
       have i₂ := eq916048
       grind)
    | exact superpose eq916048 eq84998
    | exact resolve eq84998 eq916048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84998
  have eq919024 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq39888 y x
       have i₂ := eq916048
       grind)
    | exact superpose eq916048 eq39888
    | (have j0 := eq39888 y x
       grind)
    | exact resolve eq39888 eq916048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq919090 : y ≠ (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq916048
  have eq919091 : (σ y) = (σ (k y x)) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq919024
  have eq919094 : (σ y) ≠ (σ y) ∨ (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq918992
  have eq919095 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq919094
  have eq919102 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq919091
       have r₂ := eq919090
       grind)
    | exact resolve eq919091 eq919090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919090 eq919091
  have eq950029 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq919102
       grind)
    | exact superpose eq919102 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq919102
       grind)
    | exact resolve eq12 eq919102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919102
  have eq950121 : (k y x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq950029
  have eq950140 : (M.op y y) = (M.op (M.op x x) (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq919095
       grind)
    | exact superpose eq919095 eq9
    | exact resolve eq9 eq919095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919095
  have eq950243 : (M.op x x) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq950140
       have i₂ := eq9 x x
       grind)
    | exact superpose eq9 eq950140
    | exact resolve eq950140 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950140
  have eq950244 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq950243
  have eq952850 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq9 (σ y) (σ x)
       have i₂ := eq950244
       grind)
    | exact superpose eq950244 eq9
    | exact resolve eq9 eq950244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950244
  have eq953044 : (M.op (σ y) (σ y)) = (σ (M.op (M.op x x) (M.op x x))) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq952850
       have i₂ := eq43 (M.op x x)
       grind)
    | exact superpose eq43 eq952850
    | exact resolve eq952850 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952850
  have eq953128 : (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq953044
       have i₂ := eq9 x x
       grind)
    | exact superpose eq9 eq953044
    | exact resolve eq953044 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953044
  have eq953173 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq953128
       have i₂ := eq43 y
       grind)
    | exact superpose eq43 eq953128
    | exact resolve eq953128 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953128
  have eq960119 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq953173
       grind)
    | exact superpose eq953173 eq10
    | exact resolve eq10 eq953173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953173
  have eq960834 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq960119
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq960119
    | exact resolve eq960119 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960119
  have eq960835 : (M.op x x) = (M.op y y) := by grind
  clear eq960834
  have eq1137072 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ y = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq900399 x y
       have i₂ := eq950121
       grind)
    | exact superpose eq950121 eq900399
    | (have j0 := eq900399 x y
       grind)
    | exact resolve eq900399 eq950121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900399 eq950121
  have eq1137077 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ y = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq1137072
  have eq1137093 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq1137077
       have i₂ := eq960835
       grind)
    | exact superpose eq960835 eq1137077
    | exact resolve eq1137077 eq960835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137077
  have eq1137094 : y = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq1137093
  have eq1137123 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq1137094
       have i₂ := eq960835
       grind)
    | exact superpose eq960835 eq1137094
    | exact resolve eq1137094 eq960835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137094
  have eq1137166 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1137123
       grind)
    | exact superpose eq1137123 eq16
    | exact resolve eq16 eq1137123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1137167 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq80 x (σ y)
       have i₂ := eq1137123
       grind)
    | exact superpose eq1137123 eq80
    | (have j0 := eq80 x (σ y)
       grind)
    | (have r₁ := eq80 x (σ y)
       have r₂ := eq1137123
       grind)
    | exact resolve eq80 eq1137123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137123
  have eq1137325 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq1137167
  have eq1137460 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq1137325
       have i₂ := eq43 y
       grind)
    | exact superpose eq43 eq1137325
    | exact resolve eq1137325 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137325
  have eq1137582 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq1137460
       have i₂ := eq960835
       grind)
    | exact superpose eq960835 eq1137460
    | exact resolve eq1137460 eq960835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137460
  have eq1137658 : (σ y) = (σ (k y x)) ∨ y = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1137582
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1137582
    | exact resolve eq1137582 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137582
  have eq1140579 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1137658
       have i₂ := eq38064 y x
       grind)
    | exact superpose eq38064 eq1137658
    | (have j1 := eq38064 y x
       grind)
    | exact resolve eq1137658 eq38064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137658
  have eq1141133 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j1 := eq39888 y x
       grind)
    | (have r₁ := eq1140579
       have r₂ := eq39888 y x
       grind)
    | exact resolve eq1140579 eq39888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140579
  have eq1141140 : (M.op x y) = (M.op x x) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq1141133
       have r₂ := eq1137166
       grind)
    | exact resolve eq1141133 eq1137166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141133
  have eq1144247 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1137166
       have i₂ := eq1141140
       grind)
    | exact superpose eq1141140 eq1137166
    | exact resolve eq1137166 eq1141140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137166 eq1141140
  have eq1144356 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq1144247
  have eq1144357 : (σ y) = (σ (k y x)) ∨ y = (M.op x x) := by grind
  clear eq1144356
  have eq1147861 : ∀ X0 : G, (k (τ X0) (k y x)) = (τ (k X0 (σ y))) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq23 X0 (k y x)
       have i₂ := eq1144357
       grind)
    | exact superpose eq1144357 eq23
    | exact resolve eq23 eq1144357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1147866 : ∀ X0 : G, (k (k y x) (τ X0)) = (τ (k (σ y) X0)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq29 (k y x) X0
       have i₂ := eq1144357
       grind)
    | exact superpose eq1144357 eq29
    | exact resolve eq29 eq1144357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144357
  have eq1148348 : ∀ X0 : G, (k (k y x) (τ X0)) = (k y (τ X0)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1147866 X0
       have i₂ := eq29 y X0
       grind)
    | exact superpose eq29 eq1147866
    | exact resolve eq1147866 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147866
  have eq1148353 : ∀ X0 : G, (k (τ X0) (k y x)) = (k (τ X0) y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1147861 X0
       have i₂ := eq23 X0 y
       grind)
    | exact superpose eq23 eq1147861
    | exact resolve eq1147861 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147861
  have eq1151920 : ∀ X0 : G, (k (k y x) X0) = (k y X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1148348 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1148348
    | exact resolve eq1148348 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148348
  have eq1153123 : ∀ X0 : G, (k (τ (k y x)) X0) = (τ (k y (σ X0))) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq23 (k y x) X0
       have i₂ := eq1151920 (σ X0)
       grind)
    | exact superpose eq1151920 eq23
    | exact resolve eq23 eq1151920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151920
  have eq1153873 : ∀ X0 : G, y = (M.op x x) ∨ (k (τ (k y x)) X0) = (k (τ y) X0) := by
    intro X0
    first
    | (have i₁ := eq1153123 X0
       have i₂ := eq23 y X0
       grind)
    | exact superpose eq23 eq1153123
    | exact resolve eq1153123 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153123
  have eq1157345 : ∀ X0 : G, (k X0 (σ (k y x))) = (σ (k (τ X0) y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (k y x)
       have i₂ := eq1148353 X0
       grind)
    | exact superpose eq1148353 eq17
    | exact resolve eq17 eq1148353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148353
  have eq1157995 : ∀ X0 : G, y = (M.op x x) ∨ (k X0 (σ y)) = (k X0 (σ (k y x))) := by
    intro X0
    first
    | (have i₁ := eq1157345 X0
       have i₂ := eq17 X0 y
       grind)
    | exact superpose eq17 eq1157345
    | exact resolve eq1157345 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1157345
  have eq1167338 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = (k X0 (σ (k y x))) := by
    intro X0
    first
    | (have i₁ := eq176730 x
       have i₂ := eq1157995 X0
       grind)
    | exact superpose eq1157995 eq176730
    | (have j1 := eq1157995 X0
       grind)
    | exact resolve eq176730 eq1157995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157995
  have eq1167749 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (σ (k y x))) := by
    intro X0
    first
    | (have j0 := eq1167338 X0
       grind)
    | (have r₁ := eq1167338 X0
       have r₂ := eq16
       grind)
    | exact resolve eq1167338 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167338
  have eq1169630 : ∀ X0 : G, (k X0 (τ (σ (k y x)))) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (σ (k y x))
       have i₂ := eq1167749 (σ X0)
       grind)
    | exact superpose eq1167749 eq29
    | exact resolve eq29 eq1167749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1167749
  have eq1170668 : ∀ X0 : G, (k (τ (σ X0)) y) = (k X0 (τ (σ (k y x)))) := by
    intro X0
    first
    | (have i₁ := eq1169630 X0
       have i₂ := eq23 (σ X0) y
       grind)
    | exact superpose eq23 eq1169630
    | exact resolve eq1169630 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1169630
  have eq1171126 : ∀ X0 : G, (k X0 (k y x)) = (k (τ (σ X0)) y) := by
    intro X0
    first
    | (have i₁ := eq1170668 X0
       have i₂ := eq10 (k y x)
       grind)
    | exact superpose eq10 eq1170668
    | exact resolve eq1170668 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170668
  have eq1171388 : ∀ X0 : G, (k X0 y) = (k X0 (k y x)) := by
    intro X0
    first
    | (have i₁ := eq1171126 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1171126
    | exact resolve eq1171126 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171126
  have eq1211077 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (τ (k y x)) X0) = (k (τ y) X0) := by
    intro X0
    first
    | (have i₁ := eq176730 x
       have i₂ := eq1153873 X0
       grind)
    | exact superpose eq1153873 eq176730
    | (have j1 := eq1153873 X0
       grind)
    | exact resolve eq176730 eq1153873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153873
  have eq1211495 : ∀ X0 : G, (k (τ (k y x)) X0) = (k (τ y) X0) := by
    intro X0
    first
    | (have j0 := eq1211077 X0
       grind)
    | (have r₁ := eq1211077 X0
       have r₂ := eq16
       grind)
    | exact resolve eq1211077 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211077
  have eq1212485 : ∀ X0 : G, (k (σ (τ (k y x))) X0) = (σ (k (τ y) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ (k y x))
       have i₂ := eq1211495 (τ X0)
       grind)
    | exact superpose eq1211495 eq18
    | exact resolve eq18 eq1211495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211495
  have eq1213202 : ∀ X0 : G, (k (σ (τ y)) X0) = (k (σ (τ (k y x))) X0) := by
    intro X0
    first
    | (have i₁ := eq1212485 X0
       have i₂ := eq18 X0 (τ y)
       grind)
    | exact superpose eq18 eq1212485
    | exact resolve eq1212485 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1212485
  have eq1214086 : ∀ X0 : G, (k (k y x) X0) = (k (σ (τ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq1213202 X0
       have i₂ := eq11 (k y x)
       grind)
    | exact superpose eq11 eq1213202
    | exact resolve eq1213202 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213202
  have eq1214471 : ∀ X0 : G, (k (k y x) X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq1214086 X0
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq1214086
    | exact resolve eq1214086 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214086
  have eq1214913 : (M.op (k y x) (k y x)) = (k y (k y x)) := by
    first
    | (have i₁ := eq34 (k y x)
       have i₂ := eq1214471 (k y x)
       grind)
    | exact superpose eq1214471 eq34
    | exact resolve eq34 eq1214471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214471
  have eq1216012 : (M.op (k y x) (k y x)) = (k y y) := by
    first
    | (have i₁ := eq1214913
       have i₂ := eq1171388 y
       grind)
    | exact superpose eq1171388 eq1214913
    | exact resolve eq1214913 eq1171388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171388 eq1214913
  have eq1216111 : (M.op y y) = (M.op (k y x) (k y x)) := by
    first
    | (have i₁ := eq1216012
       have i₂ := eq34 y
       grind)
    | exact superpose eq34 eq1216012
    | exact resolve eq1216012 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1216012
  have eq1216170 : (M.op x x) = (M.op (k y x) (k y x)) := by
    first
    | (have i₁ := eq1216111
       have i₂ := eq960835
       grind)
    | exact superpose eq960835 eq1216111
    | exact resolve eq1216111 eq960835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216111
  have eq1223356 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq199 y x
       have i₂ := eq1216170
       grind)
    | exact superpose eq1216170 eq199
    | (have j0 := eq199 y x
       grind)
    | exact resolve eq199 eq1216170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq1216170
  have eq1224264 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq1223356
       have r₂ := eq84995
       grind)
    | exact resolve eq1223356 eq84995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84995 eq1223356
  have eq1359570 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1224264
       grind)
    | exact superpose eq1224264 eq16
    | exact resolve eq16 eq1224264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1359578 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq46919 (σ y) x
       have i₂ := eq1224264
       grind)
    | exact superpose eq1224264 eq46919
    | (have j0 := eq46919 (σ y) x
       grind)
    | (have r₁ := eq46919 (σ y) x
       have r₂ := eq1224264
       grind)
    | exact resolve eq46919 eq1224264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46919
  have eq1359725 : (σ y) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq1224264
  have eq1359729 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq1359578
  have eq1359766 : (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq1359729
       have r₂ := eq1359725
       grind)
    | exact resolve eq1359729 eq1359725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359725 eq1359729
  have eq1359798 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq1359766
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1359766
    | exact resolve eq1359766 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359766
  have eq1366559 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1359798
       grind)
    | exact superpose eq1359798 eq16
    | exact resolve eq16 eq1359798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1366560 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq80 x (σ y)
       have i₂ := eq1359798
       grind)
    | exact superpose eq1359798 eq80
    | (have j0 := eq80 x (σ y)
       grind)
    | (have r₁ := eq80 x (σ y)
       have r₂ := eq1359798
       grind)
    | exact resolve eq80 eq1359798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359798
  have eq1366722 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq1366560
  have eq1366860 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq1366722
       have i₂ := eq43 y
       grind)
    | exact superpose eq43 eq1366722
    | exact resolve eq1366722 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366722
  have eq1366985 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq1366860
       have i₂ := eq960835
       grind)
    | exact superpose eq960835 eq1366860
    | exact resolve eq1366860 eq960835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366860
  have eq1367062 : (σ y) = (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1366985
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1366985
    | exact resolve eq1366985 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366985
  have eq1367752 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1367062
       have i₂ := eq38064 y x
       grind)
    | exact superpose eq38064 eq1367062
    | (have j1 := eq38064 y x
       grind)
    | exact resolve eq1367062 eq38064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38064 eq1367062
  have eq1368613 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j1 := eq39888 y x
       grind)
    | (have r₁ := eq1367752
       have r₂ := eq39888 y x
       grind)
    | exact resolve eq1367752 eq39888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39888 eq1367752
  have eq1368849 : (M.op x y) = (M.op x x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq1368613
       have r₂ := eq1366559
       grind)
    | exact resolve eq1368613 eq1366559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368613
  have eq1369585 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq1366559
       have i₂ := eq1368849
       grind)
    | exact superpose eq1368849 eq1366559
    | exact resolve eq1366559 eq1368849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1366559 eq1368849
  have eq1369698 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq1369585
  have eq1369699 : (σ y) = (σ (k y x)) := by grind
  clear eq1369698
  have eq1371213 : (k y x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq1369699
       grind)
    | exact superpose eq1369699 eq10
    | exact resolve eq10 eq1369699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1372026 : y = (k y x) := by
    first
    | (have i₁ := eq1371213
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1371213
    | exact resolve eq1371213 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371213
  have eq1373073 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ (M.op X0 X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq220196 y x x
       have i₂ := eq1372026
       grind)
    | exact superpose eq1372026 eq220196
    | exact resolve eq220196 eq1372026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220196
  have eq1376227 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1369699
       have i₂ := eq1373073 x
       grind)
    | exact superpose eq1373073 eq1369699
    | (have j1 := eq1373073 x
       grind)
    | exact resolve eq1369699 eq1373073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373073
  have eq1378984 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1376227
       grind)
    | exact superpose eq1376227 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1376227
       grind)
    | exact resolve eq12 eq1376227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376227
  have eq1379080 : (k y x) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1378984
  have eq1379180 : (k y x) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1379080
       have i₂ := eq960835
       grind)
    | exact superpose eq960835 eq1379080
    | exact resolve eq1379080 eq960835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1379080
  have eq1379214 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1379180
       have i₂ := eq1372026
       grind)
    | exact superpose eq1372026 eq1379180
    | exact resolve eq1379180 eq1372026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372026 eq1379180
  have eq1379252 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1359570
       have i₂ := eq1379214
       grind)
    | exact superpose eq1379214 eq1359570
    | (have r₁ := eq1359570
       have r₂ := eq1379214
       grind)
    | exact resolve eq1359570 eq1379214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359570 eq1379214
  have eq1379737 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq1379252
  have eq1381716 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq80 x (σ y)
       have i₂ := eq1379737
       grind)
    | exact superpose eq1379737 eq80
    | (have j0 := eq80 x (σ y)
       grind)
    | (have r₁ := eq80 x (σ y)
       have r₂ := eq1379737
       grind)
    | exact resolve eq80 eq1379737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq1379737
  have eq1381878 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq1381716
  have eq1382016 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1381878
       have i₂ := eq43 y
       grind)
    | exact superpose eq43 eq1381878
    | exact resolve eq1381878 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq1381878
  have eq1382139 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1382016
       have i₂ := eq960835
       grind)
    | exact superpose eq960835 eq1382016
    | exact resolve eq1382016 eq960835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960835 eq1382016
  have eq1382214 : (σ (k y x)) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1382139
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1382139
    | exact resolve eq1382139 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382139
  have eq1382274 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1382214
       have i₂ := eq1369699
       grind)
    | exact superpose eq1369699 eq1382214
    | exact resolve eq1382214 eq1369699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369699 eq1382214
  have eq1383744 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1382274
       grind)
    | exact superpose eq1382274 eq10
    | exact resolve eq10 eq1382274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382274
  have eq1384524 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1383744
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1383744
    | exact resolve eq1383744 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1383744
  have eq1384525 : y = (M.op x x) := by grind
  clear eq1384524
  have eq1384918 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq176730 x
       have i₂ := eq1384525
       grind)
    | exact superpose eq1384525 eq176730
    | exact resolve eq176730 eq1384525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176730 eq1384525
  have eq1385344 : False := by grind
  exact eq1385344

/-- `Equation3677`: `x ◇ x = (y ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_pxy_pxx_pxy_Equation3677 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3677 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3677.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
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
  clear eq22
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
  have eq50 : (M.op y y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X0 X0) X0
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq70 x y
       grind)
    | exact superpose eq70 eq44
    | (have j1 := eq70 x y
       grind)
    | exact resolve eq44 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq97
    | exact resolve eq97 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
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
  have eq121 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq121 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq121 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq121 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq129 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq125 y
       grind)
    | exact superpose eq125 eq77
    | exact resolve eq77 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq132 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq129
       have i₂ := eq125 sF3
       grind)
    | exact superpose eq125 eq129
    | exact resolve eq129 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq149 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq152 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq149
       have i₂ := eq125 sF1
       grind)
    | exact superpose eq125 eq149
    | exact resolve eq149 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq155 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq152
       have i₂ := eq125 sF0
       grind)
    | exact superpose eq125 eq152
    | exact resolve eq152 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq158 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y y)) := by
    first
    | exact superpose eq50 eq155
    | exact resolve eq155 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq155
  have eq178 : (M.op y y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq158
       grind)
    | exact superpose eq158 eq16
    | exact resolve eq16 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq132
       have i₂ := eq158
       grind)
    | exact superpose eq158 eq132
    | exact resolve eq132 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq228 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq40 eq70
    | (have j0 := eq70 (σ X0) (σ y)
       grind)
    | exact resolve eq70 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq229 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq198 eq228
    | (have j0 := eq228 X0
       grind)
    | exact resolve eq228 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq281 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq125 (τ X0)
       grind)
    | exact superpose eq125 eq34
    | exact resolve eq34 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq281 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq281
    | exact resolve eq281 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq294 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq292 X0
       have i₂ := eq125 X0
       grind)
    | exact superpose eq125 eq292
    | exact resolve eq292 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq292
  have eq609 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq16
    | exact resolve eq16 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq712 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq100 eq70
    | (have j0 := eq70 (σ x) (σ y)
       grind)
    | exact resolve eq70 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq713 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq712
    | exact resolve eq712 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq716 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq713
       have r₂ := eq27
       grind)
    | exact resolve eq713 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq718 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq198 eq716
    | exact resolve eq716 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq720 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq718
    | exact resolve eq718 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq2893 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (k (τ X0) y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq229 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq229
    | exact resolve eq229 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq2959 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2893 X0
       have i₂ := eq34 X0 y
       grind)
    | exact superpose eq34 eq2893
    | (have j0 := eq2893 X0
       grind)
    | exact resolve eq2893 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq2893
  have eq2968 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2959 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2959
    | (have j0 := eq2959 X0
       grind)
    | exact resolve eq2959 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2959
  have eq25409 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) X0) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq2968 eq12
    | (have j0 := eq12 X0 (σ y)
       have j1 := eq2968 X0
       grind)
    | exact resolve eq12 eq2968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25436 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq25409 X0
       have j1 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq25409 X0
       have r₂ := eq13 X0 (σ y)
       grind)
    | exact resolve eq25409 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25409
  have eq25447 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq25436 X0
       grind)
    | (have r₁ := eq25436 X0
       have r₂ := eq198
       grind)
    | exact resolve eq25436 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25436
  have eq1877725 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq100 eq25447
    | exact resolve eq25447 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq25447
  have eq1879443 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq1877725
    | exact resolve eq1877725 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877725
  have eq1879869 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq1879443
       have r₂ := eq27
       grind)
    | exact resolve eq1879443 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879443
  have eq1880530 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq1879869 eq14
    | exact resolve eq14 eq1879869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879869
  have eq1880572 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq1880530 eq720
    | exact resolve eq720 eq1880530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720 eq1880530
  have eq1883645 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq1880572
  have eq1883697 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq1883645
       have r₂ := eq27
       grind)
    | exact resolve eq1883645 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883645
  have eq1883721 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq158
       have i₂ := eq1883697
       grind)
    | exact superpose eq1883697 eq158
    | exact resolve eq158 eq1883697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq1883734 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq1883697
       grind)
    | exact superpose eq1883697 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1883697
       grind)
    | exact resolve eq12 eq1883697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1883779 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq1883721
    | exact resolve eq1883721 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883721
  have eq1883803 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ (M.op x y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq2968 eq1883779
    | (have j1 := eq2968 X0
       grind)
    | exact resolve eq1883779 eq2968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2968 eq1883779
  have eq1889993 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1883803 eq58
    | (have j1 := eq1883803 (σ x)
       grind)
    | exact resolve eq58 eq1883803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq1883803
  have eq1891000 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1889993
    | exact resolve eq1889993 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1889993
  have eq1891204 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq1891000
    | exact resolve eq1891000 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1891000
  have eq1891351 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq1891204
       have r₂ := eq27
       grind)
    | exact resolve eq1891204 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1891204
  have eq2212076 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq1883734 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1883734
    | (have j0 := eq1883734 x
       grind)
    | (have r₁ := eq1883734 x
       have r₂ := eq18
       grind)
    | exact resolve eq1883734 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883734
  have eq2212080 : y = (M.op y x) ∨ (k x y) = (M.op x x) := by grind
  clear eq2212076
  have eq2212082 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2212080
       have i₂ := eq1891351
       grind)
    | exact superpose eq1891351 eq2212080
    | exact resolve eq2212080 eq1891351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2212080
  have eq2212157 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq2212082
       grind)
    | exact superpose eq2212082 eq14
    | exact resolve eq14 eq2212082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2212082
  have eq2212166 : (τ (M.op (σ x) (σ y))) = (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2212157
       have i₂ := eq609 sF4
       grind)
    | exact superpose eq609 eq2212157
    | exact resolve eq2212157 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609 eq2212157
  have eq2212238 : (τ (M.op (σ x) (σ y))) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq51 eq2212166
    | exact resolve eq2212166 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq2212166
  have eq2212302 : (τ (M.op (σ x) (σ y))) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq198 eq2212238
    | exact resolve eq2212238 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq2212238
  have eq2212311 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq178 eq2212302
    | exact resolve eq2212302 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq2212302
  have eq2212316 : y = (M.op y x) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2212311
       have i₂ := eq1883697
       grind)
    | exact superpose eq1883697 eq2212311
    | exact resolve eq2212311 eq1883697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883697 eq2212311
  have eq2212319 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2212316
       grind)
    | exact superpose eq2212316 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2212316
       grind)
    | exact resolve eq13 eq2212316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2212316
  have eq2212330 : (M.op x y) = (k x y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq2212319
  have eq2212337 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2212330
       have i₂ := eq1891351
       grind)
    | exact superpose eq1891351 eq2212330
    | exact resolve eq2212330 eq1891351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1891351 eq2212330
  have eq2212345 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2212337
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2212337
    | exact resolve eq2212337 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2212337
  have eq2212346 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq2212345
  have eq2213039 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2212346 eq15
    | exact resolve eq15 eq2212346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2212346
  have eq2213709 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq2213039
    | exact resolve eq2213039 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2213039
  have eq2213764 : False := by grind
  exact eq2213764

/-- `Equation3690`: `x ◇ x = (y ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pyx_x_pyx_Equation3690 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3690 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3690.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (M.op X2 X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq26 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X3) = (M.op (M.op (M.op X0 X0) (M.op X1 X2)) (M.op X4 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X3 X2 X4
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq12 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (τ X1) (τ X1)) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq53 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X0 X0) (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq53
    | (have j0 := eq53 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq53 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67 y x
       grind)
    | exact superpose eq67 eq16
    | (have j1 := eq67 x y
       grind)
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq376 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq345
       have i₂ := eq53 y x
       grind)
    | exact superpose eq53 eq345
    | (have j1 := eq53 (σ x) (σ y)
       grind)
    | (have r₁ := eq345
       have r₂ := eq53 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq345
       have r₂ := eq53 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq345 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq345
  have eq381 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq376
  have eq459 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) (M.op X3 (σ X4))) ≠ (M.op (σ X5) (σ X5)) ∨ (σ (k X4 X5)) = (M.op (σ X5) (σ X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq40 X4 X5
       have i₂ := eq26 X0 X1 X2 (σ X4) X3
       grind)
    | exact superpose eq26 eq40
    | (have j0 := eq40 X4 X5
       grind)
    | exact resolve eq40 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq40 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq653 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq42 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq654 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq653 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq653
    | exact resolve eq653 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq662 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq654 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq654
    | exact resolve eq654 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq690 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq662 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq662
    | exact resolve eq662 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq761 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq469 X0
       have i₂ := eq690 X0
       grind)
    | exact superpose eq690 eq469
    | exact resolve eq469 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq29671 : ∀ X0 X1 X2 X3 X4 X5 : G, (σ (k X4 X5)) = (M.op (σ X5) (σ X4)) ∨ (M.op (M.op (M.op X0 X0) (M.op X1 X2)) (M.op X3 (σ X4))) ≠ (σ (M.op X5 X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq459 X0 X1 X2 X3 X4 X5
       have i₂ := eq761 X5
       grind)
    | exact superpose eq761 eq459
    | (have j0 := eq459 X0 X1 X2 X3 X4 X5
       grind)
    | exact resolve eq459 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq29752 : ∀ X0 X1 X2 X3 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) ≠ (M.op (M.op (M.op X0 X0) (M.op X1 X2)) (M.op X3 (σ y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16
       have i₂ := eq29671 X0 X1 X2 X3 y x
       grind)
    | exact superpose eq29671 eq16
    | (have j1 := eq29671 X0 X1 X2 X3 y x
       grind)
    | exact resolve eq16 eq29671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29671
  have eq30086 : (σ (M.op x x)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq29752 x x x x
       have i₂ := eq26 x x x (σ y) x
       grind)
    | exact superpose eq26 eq29752
    | exact resolve eq29752 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq29752
  have eq30162 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) ≠ (σ (M.op y y)) := by
    first
    | (have i₁ := eq30086
       have i₂ := eq761 y
       grind)
    | exact superpose eq761 eq30086
    | exact resolve eq30086 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761 eq30086
  have eq66672 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq30162
       have i₂ := eq381
       grind)
    | exact superpose eq381 eq30162
    | exact resolve eq30162 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq66691 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq66672
  have eq66693 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq66691
       have r₂ := eq690 x
       grind)
    | exact resolve eq66691 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66691
  have eq66706 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq66693
       grind)
    | exact superpose eq66693 eq10
    | exact resolve eq10 eq66693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66693
  have eq66790 : x = y := by
    first
    | (have i₁ := eq66706
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq66706
    | exact resolve eq66706 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66706
  have eq66810 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq30162
       have i₂ := eq66790
       grind)
    | exact superpose eq66790 eq30162
    | exact resolve eq30162 eq66790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30162 eq66790
  have eq66811 : (σ (M.op x x)) ≠ (σ (k x x)) := by grind
  clear eq66810
  have eq66812 : False := by grind
  exact eq66812

/-- `Equation3690`: `x ◇ x = (y ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pxx_y_pyx_Equation3690 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3690 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3690.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (M.op X2 X0)) := by
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
  have eq55 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X2) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 (M.op x x)
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1 x
       have i₂ := eq14 X0 x X0
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq72 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (M.op (M.op X2 X0) (M.op X2 X0)) = (k (M.op X2 X0) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X2 X0) (M.op X1 X1)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X2 X0) (M.op X1 X1)
       grind)
    | (have r₁ := eq13 (M.op X2 (M.op X1 X1)) (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (M.op x y) ≠ (M.op x x) ∨ (M.op y y) = (k y x) := by
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
  have eq74 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op (M.op X2 X0) (M.op X2 X0)) = (k (M.op X2 X0) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 X0 X1 X2
       have i₂ := eq14 X1 X1 X1
       grind)
    | exact superpose eq14 eq72
    | (have j0 := eq72 X0 X1 X2
       grind)
    | (have r₁ := eq72 X0 X0 X2
       have r₂ := eq14 X0 X0 X0
       grind)
    | (have r₁ := eq72 (M.op (M.op X1 X1) (M.op X1 X1)) X1 X2
       have r₂ := eq14 (M.op X1 X1) (M.op X1 X1) (M.op X1 X1)
       grind)
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq80 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq75 x
       grind)
    | exact superpose eq75 eq43
    | exact resolve eq43 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq81 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq75 sF2
       grind)
    | exact superpose eq75 eq49
    | exact resolve eq49 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq82 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq81
       have i₂ := eq75 x
       grind)
    | exact superpose eq75 eq81
    | exact resolve eq81 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq83 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq80
       have i₂ := eq75 sF2
       grind)
    | exact superpose eq75 eq80
    | exact resolve eq80 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq89 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (k y x) := by
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
  have eq90 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k (M.op X2 X0) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (M.op X2 X0) (M.op X1 X1)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq11
    | exact resolve eq11 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
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
  have eq107 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X2 X2) (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X1 X1
       have i₂ := eq11 X0 X1
       grind)
    | (have i₁ := eq14 X0 X1 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq14
    | (have j1 := eq11 X1 X0
       grind)
    | exact resolve eq14 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq11 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq111 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq126 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k (M.op X2 X0) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100 X0 X1 X2
       have i₂ := eq14 X1 X1 X1
       grind)
    | exact superpose eq14 eq100
    | (have j0 := eq100 X0 X1 X2
       grind)
    | exact resolve eq100 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq127 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k (M.op X2 X0) (M.op X1 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq126 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq135 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq136 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq24 eq36
  have eq138 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq136
       have i₂ := eq75 sF3
       grind)
    | exact superpose eq75 eq136
    | exact resolve eq136 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq140 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq138
       have i₂ := eq75 y
       grind)
    | exact superpose eq75 eq138
    | exact resolve eq138 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq146 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq135
       grind)
    | exact superpose eq135 eq16
    | exact resolve eq16 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq162 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq161
       have i₂ := eq75 sF1
       grind)
    | exact superpose eq75 eq161
    | exact resolve eq161 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq164 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq162
       have i₂ := eq75 sF0
       grind)
    | exact superpose eq75 eq162
    | exact resolve eq162 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq162
  have eq203 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq164 eq16
    | exact resolve eq16 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 X0) (M.op y y)) := by
    intro X0
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : (M.op y y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq256 x
       have i₂ := eq14 y x y
       grind)
    | exact superpose eq14 eq256
    | exact resolve eq256 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq260 : (σ (M.op y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq257 eq164
    | exact resolve eq164 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq269 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq260
       have i₂ := eq140
       grind)
    | exact superpose eq140 eq260
    | exact resolve eq260 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq275 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 X0) (M.op (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq275 x
       have i₂ := eq14 sF3 x sF3
       grind)
    | exact superpose eq14 eq275
    | exact resolve eq275 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq481 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X1 X1
       have i₂ := eq11 X0 X1
       grind)
    | (have i₁ := eq59 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq59
    | (have j1 := eq11 X1 X0
       grind)
    | exact resolve eq59 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq481 X0 X1
       have i₂ := eq59 X1 X0
       grind)
    | exact superpose eq59 eq481
    | (have j0 := eq481 X0 X1
       grind)
    | exact resolve eq481 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq766 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq269 eq74
    | exact resolve eq74 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1193 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq135
       have i₂ := eq101
       grind)
    | exact superpose eq101 eq135
    | exact resolve eq135 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq1194 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq1193
    | exact resolve eq1193 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193
  have eq2648 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq117 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3121 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k (M.op X2 X0) (M.op X1 X1)) ∨ (M.op X0 X0) ≠ (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77 X0 X1 X2
       have i₂ := eq59 X0 X2
       grind)
    | exact superpose eq59 eq77
    | (have j0 := eq77 X0 X1 X2
       grind)
    | (have r₁ := eq77 X0 (M.op X1 X0) X2
       have r₂ := eq59 X0 X1
       grind)
    | (have r₁ := eq77 (M.op X1 X0) X0 X2
       have r₂ := eq59 X0 X1
       grind)
    | exact resolve eq77 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq77
  have eq3122 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k (M.op X2 X0) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3121 X0 X1 X2
       have j1 := eq127 X0 X1 X2
       grind)
    | (have r₁ := eq3121 X0 X1 X2
       have r₂ := eq127 X0 X1 X2
       grind)
    | (have r₁ := eq3121 X1 X0 X2
       have r₂ := eq127 X0 X1 X2
       grind)
    | exact resolve eq3121 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq3121
  have eq3194 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X3) = (M.op (k (M.op X0 X1) (M.op X2 X2)) (M.op X4 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X3 X1 X4
       have i₂ := eq3122 X1 X2 X0
       grind)
    | exact superpose eq3122 eq14
    | exact resolve eq14 eq3122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3203 : ∀ X0 X1 X2 : G, (M.op y y) = (M.op (k (M.op X0 X1) (M.op X2 X2)) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X1
       have i₂ := eq3122 X1 X2 X0
       grind)
    | exact superpose eq3122 eq56
    | exact resolve eq56 eq3122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3122
  have eq4276 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 X0) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq107 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107
    | (have j0 := eq107 x y X0
       grind)
    | exact resolve eq107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4278 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq107
    | (have j0 := eq107 (σ x) (σ y) X0
       grind)
    | exact resolve eq107 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq4386 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq57 eq4278
    | exact resolve eq4278 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq4278
  have eq4387 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq56 eq4276
    | exact resolve eq4276 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq4276
  have eq4397 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq269 eq4386
    | exact resolve eq4386 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4386
  have eq22492 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1194 eq4397
    | exact resolve eq4397 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22495 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1194 eq117
    | (have j0 := eq117 (σ x) (σ y)
       grind)
    | exact resolve eq117 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq1194
  have eq22496 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq269 eq22495
    | exact resolve eq22495 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22495
  have eq22499 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq22492
       have r₂ := eq27
       grind)
    | exact resolve eq22492 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22492
  have eq22515 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq22496
    | exact resolve eq22496 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22496
  have eq22523 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq22515
    | exact resolve eq22515 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22515
  have eq22531 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq22523
       have r₂ := eq27
       grind)
    | exact resolve eq22523 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22523
  have eq23003 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq22531 eq22499
    | exact resolve eq22499 eq22531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22499 eq22531
  have eq23139 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq23003
  have eq23187 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq23139
       have r₂ := eq27
       grind)
    | exact resolve eq23139 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23139
  have eq23205 : (M.op x y) ≠ (M.op x y) ∨ (M.op y y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq23187
       grind)
    | exact superpose eq23187 eq73
    | (have r₁ := eq73
       have r₂ := eq23187
       grind)
    | exact resolve eq73 eq23187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23347 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (k (M.op X0 X1) (M.op X2 X2)) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3194 X0 X1 X2 x x
       have i₂ := eq23187
       grind)
    | exact superpose eq23187 eq3194
    | exact resolve eq3194 eq23187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3194 eq23187
  have eq23354 : (M.op y y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23205
  have eq23357 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3203 eq23347
    | exact resolve eq23347 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3203 eq23347
  have eq24403 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq140
       have i₂ := eq23357
       grind)
    | exact superpose eq23357 eq140
    | exact resolve eq140 eq23357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23357
  have eq24627 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq269 eq24403
    | exact resolve eq24403 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24403
  have eq24648 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq24627
    | exact resolve eq24627 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24627
  have eq28708 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq135
       have i₂ := eq23354
       grind)
    | exact superpose eq23354 eq135
    | exact resolve eq135 eq23354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23354
  have eq28734 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28708
       have i₂ := eq140
       grind)
    | exact superpose eq140 eq28708
    | exact resolve eq28708 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq28708
  have eq28738 : (k (σ y) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq269 eq28734
    | exact resolve eq28734 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28734
  have eq31650 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28738 eq4397
    | exact resolve eq4397 eq28738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4397
  have eq31654 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq31650
  have eq33098 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31654 eq24648
    | exact resolve eq24648 eq31654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24648 eq31654
  have eq33260 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq33098
  have eq33323 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq33260
       have r₂ := eq27
       grind)
    | exact resolve eq33260 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33260
  have eq33372 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33323 eq90
    | (have r₁ := eq90
       have r₂ := eq33323
       grind)
    | exact resolve eq90 eq33323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq33373 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33323 eq276
    | exact resolve eq276 eq33323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276 eq33323
  have eq33397 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq33372
  have eq33405 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq269 eq33373
    | exact resolve eq33373 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq33373
  have eq35834 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2648 X0 X1
       have j1 := eq510 X1 X0
       grind)
    | (have r₁ := eq2648 X1 X0
       have r₂ := eq510 X0 X1
       grind)
    | (have r₁ := eq2648 X1 X1
       have r₂ := eq510 X1 X1
       grind)
    | (have r₁ := eq2648 X1 (M.op X1 X1)
       have r₂ := eq510 (M.op X1 X1) X1
       grind)
    | exact resolve eq2648 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510 eq2648
  have eq38255 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33397 eq146
    | exact resolve eq146 eq33397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33397
  have eq38294 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq38255
    | exact resolve eq38255 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38255
  have eq42913 : (τ (σ x)) = (M.op x x) ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38294 eq82
    | exact resolve eq82 eq38294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq38294
  have eq43203 : x = (k y x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq42913
    | exact resolve eq42913 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42913
  have eq44740 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35834 y x
       have i₂ := eq43203
       grind)
    | exact superpose eq43203 eq35834
    | (have j0 := eq35834 y x
       grind)
    | exact resolve eq35834 eq43203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43203
  have eq44747 : x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq44740
  have eq44759 : x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44747
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq44747
    | exact resolve eq44747 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq44747
  have eq44760 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq44759
  have eq44779 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq83
       have i₂ := eq44760
       grind)
    | exact superpose eq44760 eq83
    | exact resolve eq83 eq44760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq44760
  have eq45071 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44779
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44779
    | exact resolve eq44779 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44779
  have eq45089 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45071 eq766
    | exact resolve eq766 eq45071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq45094 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45071 eq33405
    | exact resolve eq33405 eq45071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33405 eq45071
  have eq45309 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq45094
  have eq45370 : (k (σ y) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq45089
       have r₂ := eq28738
       grind)
    | exact resolve eq45089 eq28738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28738 eq45089
  have eq45387 : (τ (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45309 eq203
    | exact resolve eq203 eq45309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45309
  have eq45678 : (τ (σ x)) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq257 eq45387
    | exact resolve eq45387 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45387
  have eq45685 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq45678
    | exact resolve eq45678 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq45678
  have eq50706 : (k y x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45370 eq146
    | exact resolve eq146 eq45370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq45370
  have eq50734 : (k y x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq203 eq50706
    | exact resolve eq50706 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq50706
  have eq50739 : (M.op y y) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq257 eq50734
    | exact resolve eq50734 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50734
  have eq55789 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4387
       have i₂ := eq50739
       grind)
    | exact superpose eq50739 eq4387
    | exact resolve eq4387 eq50739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4387
  have eq55795 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq55789
  have eq55836 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45685
       have i₂ := eq55795
       grind)
    | exact superpose eq55795 eq45685
    | exact resolve eq45685 eq55795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45685 eq55795
  have eq56062 : x = (M.op x y) := by grind
  clear eq55836
  have eq56206 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq56062 eq20
    | exact resolve eq20 eq56062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq56210 : x ≠ x ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq56062 eq89
    | (have r₁ := eq89
       have r₂ := eq56062
       grind)
    | exact resolve eq89 eq56062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq56246 : (M.op y y) = (M.op x x) := by
    first
    | exact superpose eq56062 eq257
    | exact resolve eq257 eq56062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257 eq56062
  have eq56277 : x = (k y x) ∨ x = (M.op x x) := by grind
  clear eq56210
  have eq56329 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq56206
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq56206
    | exact resolve eq56206 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56206
  have eq56349 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq56329 eq26
    | exact resolve eq26 eq56329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq63819 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq135
       have i₂ := eq56277
       grind)
    | exact superpose eq56277 eq135
    | exact resolve eq135 eq56277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56277
  have eq63857 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq56329 eq63819
    | exact resolve eq63819 eq56329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63819
  have eq63868 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq63857
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq63857
    | exact resolve eq63857 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63857
  have eq63877 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq56329 eq63868
    | exact resolve eq63868 eq56329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63868
  have eq64929 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq63877 eq35834
    | (have j0 := eq35834 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq35834 eq63877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63877
  have eq64936 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq64929
  have eq64941 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq56349 eq64936
    | exact resolve eq64936 eq56349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64936
  have eq64955 : x = (M.op x x) := by
    first
    | (have r₁ := eq64941
       have r₂ := eq27
       grind)
    | exact resolve eq64941 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64941
  have eq64985 : x ≠ (M.op x y) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq64955
       grind)
    | exact superpose eq64955 eq73
    | exact resolve eq73 eq64955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq65351 : (M.op y y) = (k y x) := by
    first
    | (have r₁ := eq64985
       have r₂ := eq50739
       grind)
    | exact resolve eq64985 eq50739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50739 eq64985
  have eq65404 : (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq65351
       have i₂ := eq56246
       grind)
    | exact superpose eq56246 eq65351
    | exact resolve eq65351 eq56246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56246 eq65351
  have eq65437 : x = (k y x) := by
    first
    | (have i₁ := eq65404
       have i₂ := eq64955
       grind)
    | exact superpose eq64955 eq65404
    | exact resolve eq65404 eq64955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64955 eq65404
  have eq66112 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq135
       have i₂ := eq65437
       grind)
    | exact superpose eq65437 eq135
    | exact resolve eq135 eq65437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq65437
  have eq66149 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq56329 eq66112
    | exact resolve eq66112 eq56329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66112
  have eq66159 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq66149
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq66149
    | exact resolve eq66149 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq66149
  have eq66168 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq56329 eq66159
    | exact resolve eq66159 eq56329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56329 eq66159
  have eq67480 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq66168 eq35834
    | (have j0 := eq35834 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq35834 eq66168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35834 eq66168
  have eq67487 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq67480
  have eq67492 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq56349 eq67487
    | exact resolve eq67487 eq56349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56349 eq67487
  have eq67505 : False := by grind
  exact eq67505

/-- `Equation3690`: `x ◇ x = (y ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyx_pxy_pyx_Equation3690 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3690 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3690.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq105 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq2553 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq105 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq105 X0 X1
       grind)
    | exact superpose eq105 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq105 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq105 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq105 X0 X1
       grind)
    | exact resolve eq13 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq2594 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2553 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2553
  have eq2595 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2594 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2594
  have eq2623 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2595 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq2595 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq2595 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2595
  have eq2646 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2623 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2623
    | (have j0 := eq2623 X0 X1
       grind)
    | exact resolve eq2623 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2623
  have eq2647 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2646 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2646
  have eq2658 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2647 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2647
    | exact resolve eq2647 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2685 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2647 x y
       grind)
    | exact superpose eq2647 eq16
    | exact resolve eq16 eq2647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2647
  have eq2969 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq2658 X0 (τ X1)
       grind)
    | exact superpose eq2658 eq17
    | exact resolve eq17 eq2658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq2658
  have eq2988 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2969 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2969
    | exact resolve eq2969 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2969
  have eq3001 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2988 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2988
    | exact resolve eq2988 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2988
  have eq3026 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2685
       have i₂ := eq3001 x y
       grind)
    | exact superpose eq3001 eq2685
    | exact resolve eq2685 eq3001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2685 eq3001
  have eq3027 : False := by grind
  exact eq3027
