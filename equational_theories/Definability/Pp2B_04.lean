import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq56 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq56 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq56 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq60 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq57 (σ X0)
       grind)
    | exact superpose eq57 eq15
    | exact resolve eq15 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq60
    | exact resolve eq60 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq60
  have eq84 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq96 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq69 X1
       grind)
    | exact superpose eq69 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq90
  have eq330 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq96 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq13
    | (have j0 := eq13 X0 (σ X1)
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
  have eq338 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq330 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq342 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq338 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq338 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq338 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq352 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq342 X0 X1
       have j1 := eq84 X1 (σ X0)
       grind)
    | (have r₁ := eq342 X0 X0
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq342 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq342
  have eq359 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq352 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq352
    | (have j0 := eq352 X0 X1
       grind)
    | exact resolve eq352 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq360 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq359 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq366 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq360 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq360
    | exact resolve eq360 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq360 x y
       grind)
    | exact superpose eq360 eq16
    | exact resolve eq16 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq450 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq366 X0 (τ X1)
       grind)
    | exact superpose eq366 eq18
    | exact resolve eq18 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq366
  have eq479 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq450 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq450
    | exact resolve eq450 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq493 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq479 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq479
    | exact resolve eq479 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq530 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq377
       have i₂ := eq493 x y
       grind)
    | exact superpose eq493 eq377
    | exact resolve eq377 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq493
  have eq531 : False := by grind
  exact eq531

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_x_pyy_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
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
  have eq56 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) X1 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq14 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq72
    | exact resolve eq72 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq79
    | exact resolve eq79 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq88 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq104 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq16
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq124 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq147 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq124 eq16
    | exact resolve eq16 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq188 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq147
       have i₂ := eq11 sF1 sF1
       grind)
    | exact superpose eq11 eq147
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq147 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq190 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq188
  have eq206 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 X0) x) := by
    intro X0
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq349 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq59 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq59 X1 X3 x
       have i₂ := eq59 X1 X0 x
       grind)
    | (have i₁ := eq59 X0 X1 X0
       have i₂ := eq59 X0 X0 x
       grind)
    | exact superpose eq59 eq59
    | exact resolve eq59 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 X0 x X2
       have i₂ := eq59 X0 x X1
       grind)
    | (have i₁ := eq59 X2 X2 X2
       have i₂ := eq59 X2 X1 X2
       grind)
    | exact superpose eq59 eq59
    | exact resolve eq59 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 (M.op (M.op X0 X1) X0) x X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) x) X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq56 eq59
    | exact resolve eq59 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 x
       have i₂ := eq59 X1 X0 x
       grind)
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq59 X0 X0 X2
       grind)
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op (M.op X2 X2) (M.op (M.op (M.op X0 X0) X1) (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X3) X2 X1
       have i₂ := eq59 X1 X0 X3
       grind)
    | (have i₁ := eq14 (M.op X1 X1) X1 X0
       have i₂ := eq59 X0 X1 X2
       grind)
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (M.op (M.op X0 X0) X1) ∨ (k X1 (M.op X1 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 (M.op X1 X2)
       have i₂ := eq59 X1 X0 X2
       grind)
    | (have i₁ := eq13 X0 (M.op X1 X1)
       have i₂ := eq59 X0 X1 X2
       grind)
    | exact superpose eq59 eq13
    | (have j0 := eq13 X1 (M.op X1 X2)
       grind)
    | (have r₁ := eq13 (M.op X1 X1) (M.op (M.op X1 X1) (M.op X1 X1))
       have r₂ := eq59 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact resolve eq13 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq274 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq274
    | exact resolve eq274 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq588 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq67 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq589 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq588 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq916 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq364 sF0
       have i₂ := eq362 sF0 x x
       grind)
    | (have i₁ := eq364 sF0
       have i₂ := eq362 sF0 x x
       grind)
    | exact superpose eq362 eq364
    | exact resolve eq364 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq364
  have eq1026 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq349 X3 X1 x
       have i₂ := eq349 X0 X1 x
       grind)
    | (have i₁ := eq349 X0 X1 X3
       have i₂ := eq349 (M.op X3 X3) X1 X3
       grind)
    | exact superpose eq349 eq349
    | exact resolve eq349 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1037 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X1))) = (M.op (M.op X2 X2) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq349 X0 (M.op X1 X1) X3
       have i₂ := eq349 X0 X1 X1
       grind)
    | (have i₁ := eq349 X0 (M.op X1 X1) X3
       have i₂ := eq349 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq349 eq349
    | exact resolve eq349 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1069 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X2 X3) X2)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) X3
       have i₂ := eq349 X0 X1 X1
       grind)
    | (have i₁ := eq14 X0 (M.op X1 X1) X2
       have i₂ := eq349 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq349 eq14
    | exact resolve eq14 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1070 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X1 X1)
       have i₂ := eq349 X0 X1 X1
       grind)
    | (have i₁ := eq56 (M.op X1 X1)
       have i₂ := eq349 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq349 eq56
    | exact resolve eq56 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1074 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq59 X2 (M.op X1 X1) X3
       have i₂ := eq349 X0 X1 X1
       grind)
    | (have i₁ := eq59 X0 (M.op X1 X1) X2
       have i₂ := eq349 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq349 eq59
    | exact resolve eq59 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1076 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op X1 X1)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq206 (M.op X1 X1)
       have i₂ := eq349 X0 X1 X1
       grind)
    | (have i₁ := eq206 (M.op X1 X1)
       have i₂ := eq349 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq349 eq206
    | exact resolve eq206 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1078 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) X2) = (M.op (M.op X3 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq361 (M.op X1 X1) X2 X3
       have i₂ := eq349 X0 X1 X1
       grind)
    | (have i₁ := eq361 (M.op X1 X1) X1 X3
       have i₂ := eq349 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq349 eq361
    | exact resolve eq361 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq1118 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1037 X0 X1 x X3
       have i₂ := eq58 X0 x X1
       grind)
    | exact superpose eq58 eq1037
    | exact resolve eq1037 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq1037
  have eq1135 : ∀ X0 X1 : G, (M.op x (M.op (M.op (M.op x y) X0) (M.op x y))) = (M.op (M.op X1 X1) (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq916 eq59
    | exact resolve eq59 eq916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq916
  have eq1138 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1135 x x
       have i₂ := eq14 sF0 x x
       grind)
    | exact superpose eq14 eq1135
    | exact resolve eq1135 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq1422 : ∀ X0 X1 : G, (M.op x y) = (M.op x (M.op (M.op X0 (M.op X1 X1)) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1138 (M.op X1 X1)
       have i₂ := eq1026 sF0 X1 x
       grind)
    | (have i₁ := eq1138 (M.op X1 X1)
       have i₂ := eq1026 X0 X1 sF0
       grind)
    | exact superpose eq1026 eq1138
    | exact resolve eq1138 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138
  have eq2736 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) X3) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2)) = X2 := by
    intro X0 X1 X2 X3
    by_contra hcon
    push Not at hcon
    have f2736_12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op X0 X1) X0)) = X0 := by
      intro X0 X1 X2
      grind
    have f2736_13 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
      intro X0 X1 X2
      grind
    have f2736_22 : X2 ≠ (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) X3) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2)) := by grind
    have f2736_62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) X3) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2)) = X2 := by
      intro X0 X1 X2 X3
      first
      | (have i₁ := f2736_12 (M.op X2 X2) (M.op X1 X1) X2
         have i₂ := f2736_13 X0 X1 X2
         grind)
      | (have i₁ := f2736_12 X0 (M.op X1 X1) X2
         have i₂ := f2736_13 X0 X1 X2
         grind)
      | exact superpose f2736_13 f2736_12
      | exact resolve f2736_12 f2736_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2736_126 : ∀ X0 : G, X2 ≠ (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) X3) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2)) := by
      intro X0
      first
      | (have i₁ := f2736_22
         have i₂ := f2736_13 X0 X1 X0
         grind)
      | (have i₁ := f2736_22
         have i₂ := f2736_13 (M.op X0 X0) X1 x
         grind)
      | exact superpose f2736_13 f2736_22
      | exact resolve f2736_22 f2736_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2736_127 : False := by
      first
      | (have r₁ := f2736_126 x
         have r₂ := f2736_62 x X1 X2 X3
         grind)
      | exact resolve f2736_126 f2736_62
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f2736_127
  clear eq349
  have eq3120 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq589 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq589
    | (have j0 := eq589 (τ X0)
       grind)
    | exact resolve eq589 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq3128 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3120 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3120
    | (have j0 := eq3120 X0
       grind)
    | exact resolve eq3120 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3120
  have eq3134 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3128 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3128
    | (have j0 := eq3128 X0
       grind)
    | exact resolve eq3128 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3128
  have eq3146 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq3134 (τ X0)
       have i₂ := eq480 X0 X0
       grind)
    | exact superpose eq480 eq3134
    | (have j0 := eq3134 (τ X0)
       grind)
    | exact resolve eq3134 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq3330 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op (M.op (M.op X0 X1) X0) X2)) ≠ X0 ∨ (M.op (M.op (M.op X0 X1) X0) X2) = (k (M.op (M.op (M.op X0 X1) X0) X2) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq376 X0 (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op X0 X1) X0)
       have i₂ := eq363 X0 X1 X2
       grind)
    | exact superpose eq363 eq376
    | exact resolve eq376 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3361 : ∀ X0 : G, (M.op (M.op x y) x) ≠ (M.op x X0) ∨ x = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq376 x x X0
       have i₂ := eq206 x
       grind)
    | exact superpose eq206 eq376
    | (have j0 := eq376 X0 x X0
       grind)
    | exact resolve eq376 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq376
  have eq4217 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X3) (M.op (M.op (M.op X4 X4) (M.op (M.op (M.op X0 X1) X0) X2)) X0)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq375 X0 (M.op (M.op (M.op X0 X1) X0) X2) X2 (M.op (M.op X0 X1) X0)
       have i₂ := eq363 X0 X1 X2
       grind)
    | exact superpose eq363 eq375
    | exact resolve eq375 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363 eq375
  have eq20459 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq80 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20460 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq20459
    | exact resolve eq20459 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20459
  have eq20471 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq20460
       have r₂ := eq27
       grind)
    | exact resolve eq20460 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20460
  have eq20527 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20471 eq13
    | (have j0 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq20471
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq20471
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq20471
       grind)
    | exact resolve eq13 eq20471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20471
  have eq20539 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq20527
  have eq20546 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20539 eq104
    | exact resolve eq104 eq20539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq20539
  have eq20585 : y = (k y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq20546
    | exact resolve eq20546 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20546
  have eq20588 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq3134 y
       grind)
    | (have r₁ := eq20585
       have r₂ := eq3134 y
       grind)
    | exact resolve eq20585 eq3134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3134 eq20585
  have eq20589 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20588 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq20588
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq20588
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq20588
       grind)
    | exact resolve eq13 eq20588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20588
  have eq20601 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq20589
  have eq20606 : (τ (σ x)) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20601 eq55
    | exact resolve eq55 eq20601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq20607 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20601 eq80
    | exact resolve eq80 eq20601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq20601
  have eq20619 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by grind
  clear eq20607
  have eq20627 : x = (k x y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28 eq20606
    | exact resolve eq20606 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20606
  have eq20630 : y = (M.op y y) ∨ x = (k x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq20627
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq20627
       have r₂ := eq13 x y
       grind)
    | exact resolve eq20627 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20627
  have eq20631 : ∀ X0 : G, y ≠ y ∨ y = (M.op y X0) ∨ y = (k X0 y) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq20630
       grind)
    | exact superpose eq20630 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq20630
       grind)
    | exact resolve eq12 eq20630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20632 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 X1) X0)) = X0 ∨ x = (k x y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 y X1
       have i₂ := eq20630
       grind)
    | exact superpose eq20630 eq14
    | exact resolve eq14 eq20630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20661 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (k x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1026 X0 y x
       have i₂ := eq20630
       grind)
    | exact superpose eq20630 eq1026
    | exact resolve eq1026 eq20630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20673 : ∀ X0 X1 : G, y = (M.op X0 (M.op X1 y)) ∨ x = (k x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1118 X0 y x
       have i₂ := eq20630
       grind)
    | exact superpose eq20630 eq1118
    | exact resolve eq1118 eq20630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118
  have eq20684 : y ≠ y ∨ y = (k y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq20630
       grind)
    | exact superpose eq20630 eq13
    | (have j0 := eq13 y y
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq20630
       grind)
    | exact resolve eq13 eq20630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20696 : y = (k y y) ∨ x = (k x y) := by grind
  clear eq20684
  have eq20697 : ∀ X0 : G, y = (k X0 y) ∨ y = (M.op y X0) ∨ x = (k x y) := by
    intro X0
    first
    | (have j0 := eq20631 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20631
  have eq20711 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq589 y
       have i₂ := eq20696
       grind)
    | exact superpose eq20696 eq589
    | (have j0 := eq589 y
       grind)
    | exact resolve eq589 eq20696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20696
  have eq20728 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (k x y) := by grind
  clear eq20711
  have eq20740 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq20728
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20728
    | exact resolve eq20728 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20728
  have eq20790 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ x = (k x y) := by
    intro X0 X1
    first
    | exact superpose eq20740 eq1026
    | exact resolve eq1026 eq20740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20990 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq20661 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20661
    | (have j0 := eq20661 x X0
       grind)
    | exact resolve eq20661 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20661
  have eq21530 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op x y)) x) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq1076 X0 y
       have i₂ := eq20990 y
       grind)
    | exact superpose eq20990 eq1076
    | exact resolve eq1076 eq20990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21591 : y = (M.op x y) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq20630
       have i₂ := eq20990 y
       grind)
    | exact superpose eq20990 eq20630
    | exact resolve eq20630 eq20990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20630
  have eq21599 : x = (k x y) ∨ y = (M.op x y) := by grind
  clear eq21591
  have eq22080 : ∀ X0 : G, y = (M.op X0 (M.op x y)) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq20673 X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20673
    | (have j0 := eq20673 X0 x
       grind)
    | exact resolve eq20673 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22229 : y ≠ (M.op (M.op x y) x) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq3361 (M.op x y)
       have i₂ := eq20673 x x
       grind)
    | exact superpose eq20673 eq3361
    | exact resolve eq3361 eq20673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3361 eq20673
  have eq22239 : y ≠ (M.op (M.op x y) x) ∨ x = (k x y) := by grind
  clear eq22229
  have eq22516 : ∀ X0 : G, y ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (k X0 (M.op x y)) ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq22080 eq12
    | (have j0 := eq12 X0 (M.op x y)
       grind)
    | exact resolve eq12 eq22080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22630 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ y = (k X0 (M.op x y)) ∨ x = (k x y) := by
    intro X0
    first
    | (have j0 := eq22516 X0
       grind)
    | (have r₁ := eq22516 X0
       have r₂ := eq21599
       grind)
    | exact resolve eq22516 eq21599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22516
  have eq23174 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq26 eq20790
    | (have j0 := eq20790 (σ x) X0
       grind)
    | exact resolve eq20790 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20790
  have eq23541 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | exact superpose eq23174 eq20740
    | exact resolve eq20740 eq23174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20740 eq23174
  have eq23546 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq23541
  have eq23553 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq23546
       grind)
    | exact superpose eq23546 eq44
    | exact resolve eq44 eq23546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23546
  have eq23579 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23553
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23553
    | exact resolve eq23553 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23553
  have eq28891 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq1026 X0 y x
       have i₂ := eq20619
       grind)
    | exact superpose eq20619 eq1026
    | exact resolve eq1026 eq20619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28921 : y ≠ y ∨ y = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq20619
       grind)
    | exact superpose eq20619 eq13
    | (have j0 := eq13 y y
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq20619
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq20619
       grind)
    | exact resolve eq13 eq20619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28937 : y = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by grind
  clear eq28921
  have eq28952 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq589 y
       have i₂ := eq28937
       grind)
    | exact superpose eq28937 eq589
    | (have j0 := eq589 y
       grind)
    | exact resolve eq589 eq28937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589 eq28937
  have eq28969 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by grind
  clear eq28952
  have eq28981 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq28969
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq28969
    | exact resolve eq28969 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28969
  have eq29040 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq28981 eq1026
    | exact resolve eq1026 eq28981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30578 : ∀ X0 : G, (M.op y (M.op (M.op x y) X0)) = X0 ∨ x = (k x y) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq20632 X0 y
       have i₂ := eq20990 X0
       grind)
    | (have i₁ := eq20632 x y
       have i₂ := eq20990 X0
       grind)
    | exact superpose eq20990 eq20632
    | exact resolve eq20632 eq20990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20632 eq20990
  have eq30904 : ∀ X0 : G, (M.op y (M.op (M.op x y) X0)) = X0 ∨ x = (k x y) := by
    intro X0
    first
    | (have j0 := eq30578 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30578
  have eq226731 : x ≠ y ∨ y = (M.op y x) ∨ x = (k x y) := by
    first
    | (have j0 := eq20697 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20697
  have eq226776 : x ≠ y ∨ x = (k x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq226731
       have r₂ := eq13 x y
       grind)
    | exact resolve eq226731 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226731
  have eq228141 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq28891 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28891
    | (have j0 := eq28891 x X0
       grind)
    | exact resolve eq28891 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28891
  have eq229579 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq20619
       have i₂ := eq228141 y
       grind)
    | exact superpose eq228141 eq20619
    | exact resolve eq20619 eq228141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20619 eq228141
  have eq229640 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq229579
  have eq229674 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op y y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq229640
       grind)
    | exact superpose eq229640 eq14
    | exact resolve eq14 eq229640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264337 : ∀ X0 : G, (M.op y (M.op x y)) = X0 ∨ x = (k x y) ∨ y = (k X0 (M.op x y)) ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq22630 eq30904
    | (have j1 := eq22630 X0
       grind)
    | exact resolve eq30904 eq22630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30904
  have eq264401 : y ≠ (M.op x y) ∨ x = (k x y) ∨ y = (k x (M.op x y)) ∨ x = (k x y) := by
    first
    | exact superpose eq22630 eq22239
    | (have j1 := eq22630 x
       grind)
    | exact resolve eq22239 eq22630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22630
  have eq264896 : y ≠ (M.op x y) ∨ x = (k x y) ∨ y = (k x (M.op x y)) := by grind
  clear eq264401
  have eq264934 : ∀ X0 : G, y = (k X0 (M.op x y)) ∨ x = (k x y) ∨ (M.op y (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq264337 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264337
  have eq264981 : y = (k x (M.op x y)) ∨ x = (k x y) := by
    first
    | (have r₁ := eq264896
       have r₂ := eq21599
       grind)
    | exact resolve eq264896 eq21599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21599 eq264896
  have eq268261 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq29040
    | (have j0 := eq29040 (σ x) X0
       grind)
    | exact resolve eq29040 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29040
  have eq269840 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq268261 eq28981
    | exact resolve eq28981 eq268261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28981 eq268261
  have eq269876 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq269840
  have eq270656 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op y y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq269876
       grind)
    | exact superpose eq269876 eq14
    | exact resolve eq14 eq269876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302544 : x = (M.op y (M.op (M.op x y) x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1070 (M.op x x) y
       have i₂ := eq229674 x
       grind)
    | exact superpose eq229674 eq1070
    | exact resolve eq1070 eq229674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302548 : (M.op (M.op x y) x) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1076 (M.op x x) y
       have i₂ := eq229674 x
       grind)
    | exact superpose eq229674 eq1076
    | exact resolve eq1076 eq229674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302618 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1026 X0 (M.op y y) x
       have i₂ := eq229674 y
       grind)
    | exact superpose eq229674 eq1026
    | exact resolve eq1026 eq229674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229674
  have eq309111 : x = (M.op y (M.op y x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq302548 eq302544
    | exact resolve eq302544 eq302548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302544 eq302548
  have eq309187 : x = (M.op y (M.op y x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq309111
  have eq312598 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq302618 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq302618
    | (have j0 := eq302618 x X0
       grind)
    | exact resolve eq302618 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302618
  have eq326873 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq309187
       have i₂ := eq229640
       grind)
    | exact superpose eq229640 eq309187
    | exact resolve eq309187 eq229640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229640 eq309187
  have eq326955 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq326873
  have eq327044 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq312598 y
       have i₂ := eq326955
       grind)
    | exact superpose eq326955 eq312598
    | exact resolve eq312598 eq326955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312598 eq326955
  have eq327280 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq327044
  have eq327348 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq327280 eq28
    | exact resolve eq28 eq327280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327280
  have eq327739 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq327348
    | exact resolve eq327348 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327348
  have eq327740 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq327739
  have eq327741 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq327740 eq20
    | exact resolve eq20 eq327740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327740
  have eq328205 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq327741
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq327741
    | exact resolve eq327741 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327741
  have eq328368 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq328205 eq23579
    | exact resolve eq23579 eq328205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23579
  have eq328537 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq328368
       have r₂ := eq27
       grind)
    | exact resolve eq328368 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328368
  have eq329756 : (τ (σ x)) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq328537 eq64
    | exact resolve eq64 eq328537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq328537
  have eq329791 : x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq329756
    | exact resolve eq329756 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329756
  have eq329810 : x = y ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq329791 eq264981
    | exact resolve eq264981 eq329791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264981 eq329791
  have eq329836 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq329810
       have r₂ := eq226776
       grind)
    | exact resolve eq329810 eq226776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226776 eq329810
  have eq449321 : ∀ X0 : G, (M.op x y) ≠ (M.op (M.op X0 X0) (M.op (M.op x y) x)) ∨ (M.op (M.op x y) x) = (k (M.op (M.op x y) x) (M.op x y)) ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq21530 eq3330
    | exact resolve eq3330 eq21530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3330 eq21530
  have eq449561 : x ≠ (M.op x y) ∨ (M.op (M.op x y) x) = (k (M.op (M.op x y) x) (M.op x y)) ∨ x = (k x y) := by
    first
    | exact superpose eq56 eq449321
    | exact resolve eq449321 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq449321
  have eq449718 : (M.op (M.op x y) x) = (k (M.op (M.op x y) x) (M.op x y)) ∨ x = (k x y) := by
    first
    | (have r₁ := eq449561
       have r₂ := eq329836
       grind)
    | exact resolve eq449561 eq329836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329836 eq449561
  have eq1779692 : y = (M.op (M.op x y) x) ∨ x = (k x y) ∨ x = (k x y) ∨ (M.op (M.op x y) x) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq264934 eq449718
    | (have j1 := eq264934 (M.op (M.op x y) x)
       grind)
    | exact resolve eq449718 eq264934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264934 eq449718
  have eq1781010 : y = (M.op (M.op x y) x) ∨ x = (k x y) ∨ (M.op (M.op x y) x) = (M.op y (M.op x y)) := by grind
  clear eq1779692
  have eq1781575 : (M.op (M.op x y) x) = (M.op y (M.op x y)) ∨ x = (k x y) := by
    first
    | (have r₁ := eq1781010
       have r₂ := eq22239
       grind)
    | exact resolve eq1781010 eq22239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1781010
  have eq1781886 : y ≠ (M.op y (M.op x y)) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | exact superpose eq1781575 eq22239
    | exact resolve eq22239 eq1781575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22239 eq1781575
  have eq1782100 : y ≠ (M.op y (M.op x y)) ∨ x = (k x y) := by grind
  clear eq1781886
  have eq1782126 : x = (k x y) := by
    first
    | (have r₁ := eq1782100
       have r₂ := eq22080 y
       grind)
    | exact resolve eq1782100 eq22080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22080 eq1782100
  have eq1782139 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1782126
       grind)
    | exact superpose eq1782126 eq44
    | exact resolve eq44 eq1782126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq1782437 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1782139
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1782139
    | exact resolve eq1782139 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1782139
  have eq1783273 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1782437 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq1782437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1782437
  have eq1783316 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq1783273
    | exact resolve eq1783273 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1783273
  have eq1797617 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1783316 eq13
    | (have j0 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq1783316
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1783316
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1783316
       grind)
    | exact resolve eq13 eq1783316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1783316
  have eq1797724 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq1797617
  have eq1797898 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1797724 eq3146
    | (have j0 := eq3146 (σ y)
       grind)
    | exact resolve eq3146 eq1797724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3146 eq1797724
  have eq1798079 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq1797898
  have eq1798096 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq1798079
    | exact resolve eq1798079 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1798079
  have eq1939033 : x = (M.op y (M.op (M.op x y) x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1070 (M.op x x) y
       have i₂ := eq270656 x
       grind)
    | exact superpose eq270656 eq1070
    | exact resolve eq1070 eq270656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070
  have eq1939037 : (M.op (M.op x y) x) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1076 (M.op x x) y
       have i₂ := eq270656 x
       grind)
    | exact superpose eq270656 eq1076
    | exact resolve eq1076 eq270656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1939123 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1026 X0 (M.op y y) x
       have i₂ := eq270656 y
       grind)
    | exact superpose eq270656 eq1026
    | exact resolve eq1026 eq270656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270656
  have eq1942190 : x = (M.op y (M.op y x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1939037 eq1939033
    | exact resolve eq1939033 eq1939037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1939033 eq1939037
  have eq1942347 : x = (M.op y (M.op y x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1942190
  have eq1944835 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1939123 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1939123
    | (have j0 := eq1939123 x X0
       grind)
    | exact resolve eq1939123 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1939123
  have eq1966662 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1942347
       have i₂ := eq269876
       grind)
    | exact superpose eq269876 eq1942347
    | exact resolve eq1942347 eq269876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269876 eq1942347
  have eq1966838 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1966662
  have eq1967012 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1944835 y
       have i₂ := eq1966838
       grind)
    | exact superpose eq1966838 eq1944835
    | exact resolve eq1944835 eq1966838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1944835 eq1966838
  have eq1967495 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1967012
  have eq1967660 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1967495 eq27
    | exact resolve eq27 eq1967495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1967495
  have eq1967968 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1967660
       have r₂ := eq328205
       grind)
    | exact resolve eq1967660 eq328205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328205 eq1967660
  have eq1967971 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1967968 eq28
    | exact resolve eq28 eq1967968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1967968
  have eq1968935 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq1967971
    | exact resolve eq1967971 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1967971
  have eq1968936 : x = (M.op x y) := by grind
  clear eq1968935
  have eq1968959 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1968936 eq20
    | exact resolve eq20 eq1968936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1969045 : ∀ X0 X1 : G, x = (M.op x (M.op (M.op X0 (M.op X1 X1)) x)) := by
    intro X0 X1
    first
    | exact superpose eq1968936 eq1422
    | exact resolve eq1422 eq1968936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422
  have eq1970311 : x = (M.op x (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq1969045 x x
       have i₂ := eq1076 x x
       grind)
    | exact superpose eq1076 eq1969045
    | exact resolve eq1969045 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076 eq1969045
  have eq1970386 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1968959
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1968959
    | exact resolve eq1968959 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1968959
  have eq1970476 : x = (M.op x (M.op x x)) := by
    first
    | exact superpose eq1968936 eq1970311
    | exact resolve eq1970311 eq1968936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1970311
  have eq1970539 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1970386 eq26
    | exact resolve eq26 eq1970386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1971197 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1970386 eq1798096
    | exact resolve eq1798096 eq1970386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1971208 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1971197
       have r₂ := eq27
       grind)
    | exact resolve eq1971197 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1971197
  have eq1974850 : ∀ X0 : G, x = (M.op X0 (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq1970476
       have i₂ := eq1026 x x X0
       grind)
    | (have i₁ := eq1970476
       have i₂ := eq1026 X0 x x
       grind)
    | exact superpose eq1026 eq1970476
    | exact resolve eq1970476 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026
  have eq1974871 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1069 x x X0 X1
       have i₂ := eq1970476
       grind)
    | exact superpose eq1970476 eq1069
    | exact resolve eq1069 eq1970476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq1974874 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1074 x x X0 X1
       have i₂ := eq1970476
       grind)
    | exact superpose eq1970476 eq1074
    | exact resolve eq1074 eq1970476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074
  have eq1974878 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1078 x x X0 X1
       have i₂ := eq1970476
       grind)
    | exact superpose eq1970476 eq1078
    | exact resolve eq1078 eq1970476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078 eq1970476
  have eq1987954 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1974871 X0 (M.op x x)
       have i₂ := eq1974850 X0
       grind)
    | exact superpose eq1974850 eq1974871
    | exact resolve eq1974871 eq1974850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1974871
  have eq1990800 : y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1987954 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1987954
    | (have j0 := eq1987954 y
       grind)
    | exact resolve eq1987954 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1991165 : y = (M.op x x) := by
    first
    | exact superpose eq1968936 eq1990800
    | exact resolve eq1990800 eq1968936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1990800
  have eq1991263 : ∀ X0 : G, x = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1974850 X0
       have i₂ := eq1991165
       grind)
    | exact superpose eq1991165 eq1974850
    | exact resolve eq1974850 eq1991165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1974850 eq1991165
  have eq2009506 : (M.op (σ y) (σ y)) = (M.op x (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1798096 eq1974874
    | exact resolve eq1974874 eq1798096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1798096
  have eq2011848 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op x (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1970386 eq2009506
    | exact resolve eq2009506 eq1970386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2009506
  have eq2012261 : (M.op (σ y) (σ y)) = (M.op x (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq2011848
       have r₂ := eq27
       grind)
    | exact resolve eq2011848 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2011848
  have eq2012417 : (M.op (σ y) (σ y)) = (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2012261
       have i₂ := eq1991263 y
       grind)
    | exact superpose eq1991263 eq2012261
    | exact resolve eq2012261 eq1991263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2012261
  have eq2082637 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq1971208
       have i₂ := eq1991263 y
       grind)
    | exact superpose eq1991263 eq1971208
    | exact resolve eq1971208 eq1991263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1971208 eq1991263
  have eq2082745 : ∀ X0 X1 X2 : G, (σ y) = (M.op (M.op X0 X0) (M.op (M.op (M.op X1 X1) (M.op (M.op (σ y) (σ y)) X2)) (σ y))) ∨ x = y := by
    intro X0 X1 X2
    first
    | exact superpose eq2082637 eq4217
    | exact resolve eq4217 eq2082637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4217
  have eq2082829 : ∀ X1 X2 : G, (σ y) = (M.op x (M.op (M.op (M.op X1 X1) (M.op (M.op (σ y) (σ y)) X2)) (σ y))) ∨ x = y := by
    intro X1 X2
    first
    | (have i₁ := eq2082745 X1 X1 X2
       have i₂ := eq1974878 (M.op (M.op (M.op X1 X1) (M.op (M.op sF3 sF3) X2)) sF3) X1
       grind)
    | exact superpose eq1974878 eq2082745
    | exact resolve eq2082745 eq1974878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2082745
  have eq2082885 : ∀ X2 : G, (σ y) = (M.op x (M.op X2 (σ y))) ∨ x = y := by
    intro X2
    first
    | (have i₁ := eq2082829 X2 x
       have i₂ := eq369 sF3 x X2
       grind)
    | exact superpose eq369 eq2082829
    | exact resolve eq2082829 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq2082829
  have eq2094291 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op x (σ y))) X1) X2) (M.op (M.op (M.op X0 X0) (M.op x (σ y))) X1)) = X1 ∨ x = y := by
    intro X0 X1 X2
    first
    | exact superpose eq2012417 eq2736
    | exact resolve eq2736 eq2012417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2736 eq2012417
  have eq2094921 : ∀ X0 X1 : G, (M.op x (M.op (M.op (M.op X0 X0) (M.op x (σ y))) X1)) = X1 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq2094291 X0 X1 X1
       have i₂ := eq1974874 (M.op (M.op (M.op X0 X0) (M.op x sF3)) X1) X1
       grind)
    | exact superpose eq1974874 eq2094291
    | exact resolve eq2094291 eq1974874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1974874 eq2094291
  have eq2095067 : ∀ X1 : G, (M.op x (M.op (M.op x (M.op x (σ y))) X1)) = X1 ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq2094921 X1 X1
       have i₂ := eq1974878 (M.op x sF3) X1
       grind)
    | exact superpose eq1974878 eq2094921
    | exact resolve eq2094921 eq1974878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1974878 eq2094921
  have eq2095122 : ∀ X1 : G, (M.op x (M.op (σ y) X1)) = X1 ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq2095067 X1
       have i₂ := eq1987954 sF3
       grind)
    | exact superpose eq1987954 eq2095067
    | exact resolve eq2095067 eq1987954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2095067
  have eq2096093 : (σ y) = (M.op x (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq1970539 eq2082885
    | (have j0 := eq2082885 (σ x)
       grind)
    | exact resolve eq2082885 eq1970539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2082885
  have eq2096542 : (M.op (σ x) (σ y)) = (M.op x (σ y)) ∨ x = y := by
    first
    | exact superpose eq2096093 eq1987954
    | exact resolve eq1987954 eq2096093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1987954 eq2096093
  have eq2114986 : (σ (M.op x y)) = (M.op x (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2082637 eq2095122
    | exact resolve eq2095122 eq2082637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2082637 eq2095122
  have eq2115318 : (σ (M.op x y)) = (M.op x (σ y)) ∨ x = y := by grind
  clear eq2114986
  have eq2115559 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2115318 eq2096542
    | exact resolve eq2096542 eq2115318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2096542 eq2115318
  have eq2115731 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq2115559
  have eq2115809 : x = y := by
    first
    | (have r₁ := eq2115731
       have r₂ := eq27
       grind)
    | exact resolve eq2115731 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2115731
  have eq2117707 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2115809
       grind)
    | exact superpose eq2115809 eq24
    | exact resolve eq24 eq2115809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2118886 : x = (k x x) := by
    first
    | (have i₁ := eq1782126
       have i₂ := eq2115809
       grind)
    | exact superpose eq2115809 eq1782126
    | exact resolve eq1782126 eq2115809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1782126 eq2115809
  have eq2119654 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2117707
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2117707
    | exact resolve eq2117707 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2117707
  have eq2120186 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1970386 eq2119654
    | exact resolve eq2119654 eq1970386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2119654
  have eq2121618 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2120186 eq1970539
    | exact resolve eq1970539 eq2120186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1970539 eq2120186
  have eq2124604 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2121618 eq190
    | exact resolve eq190 eq2121618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq2121618
  have eq2125428 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq2124604
       have r₂ := eq27
       grind)
    | exact resolve eq2124604 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2124604
  have eq2125599 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1968936 eq2125428
    | exact resolve eq2125428 eq1968936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1968936 eq2125428
  have eq2125678 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2125599
       have i₂ := eq2118886
       grind)
    | exact superpose eq2118886 eq2125599
    | exact resolve eq2125599 eq2118886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2118886 eq2125599
  have eq2125784 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2125678 eq15
    | exact resolve eq15 eq2125678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2125678
  have eq2126763 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2125784
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2125784
    | exact resolve eq2125784 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2125784
  have eq2127065 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1970386 eq2126763
    | exact resolve eq2126763 eq1970386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1970386 eq2126763
  have eq2127249 : False := by grind
  exact eq2127249

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq38 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq145 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq38 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq148 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq145 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq145 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq145 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq145 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq145 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq1391 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq148
  have eq1435 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1391 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391
  have eq2009 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1435 (σ X0) (σ X1)
       grind)
    | exact superpose eq1435 eq15
    | exact resolve eq15 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2022 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2009 X0 X1
       have i₂ := eq1435 X0 X1
       grind)
    | exact superpose eq1435 eq2009
    | exact resolve eq2009 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435 eq2009
  have eq2034 : False := by grind
  exact eq2034

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then Y else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_y_pyy_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq24 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X1) = (M.op (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) X1) X2 (M.op (M.op X1 X0) X1)
       have i₂ := eq9 X1 (M.op (M.op X1 X0) X1) X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 (τ X0))
       have i₂ := eq18 X0 X1
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
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X2 X2)) = (M.op X1 (M.op X2 X2)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq24 (M.op (M.op X1 x) X1) (M.op X2 X2) X3
       have i₂ := eq9 X1 X2 x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq180 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X1
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
  have eq190 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq180 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq191 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq190 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq242 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq56
    | (have j0 := eq56 (σ X0)
       grind)
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq292 : ∀ X0 X1 X3 : G, (M.op X1 (M.op X0 X0)) = (M.op X3 (M.op X0 X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq57 X3 X0 x
       have i₂ := eq57 X1 X0 x
       grind)
    | (have i₁ := eq57 X1 x X3
       have i₂ := eq57 (M.op X3 X3) x X3
       grind)
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq644 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq191 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq648 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq644 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq644 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq644 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq644 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq674 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq648 (τ X0) X1
       grind)
    | exact superpose eq648 eq17
    | (have j1 := eq648 X0 X1
       grind)
    | exact resolve eq17 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq678 : ∀ X0 X1 X2 : G, X1 ≠ X1 ∨ (k X2 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq648 X0 X1
       grind)
    | exact superpose eq648 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq648 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq648 X0 X1
       grind)
    | exact resolve eq12 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq702 : ∀ X0 X1 X2 : G, (k X2 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq678 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq720 : ∀ X0 X1 X2 : G, (τ X2) = (k X0 (τ X2)) ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 X2 X0
       have i₂ := eq702 X1 X2 (σ X0)
       grind)
    | exact superpose eq702 eq29
    | (have j1 := eq702 X0 (τ X2) X0
       grind)
    | exact resolve eq29 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq702
  have eq2410 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (M.op X2 (σ X0)) = (k X2 (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq720 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq720
    | (have j0 := eq720 X0 X2 (σ X0)
       grind)
    | exact resolve eq720 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq3213 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2410 X1 X2 (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2410
    | (have j0 := eq2410 X1 X2 X2
       grind)
    | exact resolve eq2410 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2410
  have eq3862 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq242 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq5509 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq674 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq674
    | (have j0 := eq674 X0 X1
       grind)
    | exact resolve eq674 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq5668 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5509 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5509
    | (have j0 := eq5509 X0 X1
       grind)
    | exact resolve eq5509 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5509
  have eq5734 : ∀ X0 X1 X2 : G, X1 ≠ X1 ∨ (k X2 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq5668 X0 X1
       grind)
    | exact superpose eq5668 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq5668 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq5668 X0 X1
       grind)
    | exact resolve eq12 eq5668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5668
  have eq5814 : ∀ X0 X1 X2 : G, (k X2 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq5734 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5734
  have eq7141 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3862 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq3862
    | (have j0 := eq3862 (τ X0)
       grind)
    | exact resolve eq3862 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq7154 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7141 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq7141
    | (have j0 := eq7141 X0
       grind)
    | exact resolve eq7141 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7141
  have eq7156 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7154 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7154
    | (have j0 := eq7154 X0
       grind)
    | exact resolve eq7154 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7154
  have eq7157 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7156 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7156
    | (have j0 := eq7156 X0
       grind)
    | exact resolve eq7156 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7156
  have eq14576 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq3213 x y X0
       grind)
    | exact superpose eq3213 eq16
    | (have j1 := eq3213 X0 y X0
       grind)
    | exact resolve eq16 eq3213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3213
  have eq14777 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq14576 X0
       have j1 := eq5814 X0 y X0
       grind)
    | (have r₁ := eq14576 X0
       have r₂ := eq5814 x y x
       grind)
    | exact resolve eq14576 eq5814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5814 eq14576
  have eq14797 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3862 y
       have i₂ := eq14777 y
       grind)
    | exact superpose eq14777 eq3862
    | (have j0 := eq3862 y
       grind)
    | exact resolve eq3862 eq14777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3862
  have eq14801 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq7157 y
       have i₂ := eq14777 y
       grind)
    | exact superpose eq14777 eq7157
    | (have j0 := eq7157 y
       grind)
    | (have r₁ := eq7157 y
       have r₂ := eq14777 y
       grind)
    | exact resolve eq7157 eq14777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7157 eq14777
  have eq14835 : y = (M.op y y) := by grind
  clear eq14801
  have eq14839 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq14797
  have eq14860 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq292 y X1 x
       have i₂ := eq14835
       grind)
    | exact superpose eq14835 eq292
    | exact resolve eq292 eq14835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15049 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq14860 y X0
       have i₂ := eq14835
       grind)
    | exact superpose eq14835 eq14860
    | exact resolve eq14860 eq14835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14835 eq14860
  have eq15923 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq292 (σ y) X1 x
       have i₂ := eq14839
       grind)
    | exact superpose eq14839 eq292
    | exact resolve eq292 eq14839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq17629 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15923 X0 (σ y)
       have i₂ := eq14839
       grind)
    | exact superpose eq14839 eq15923
    | exact resolve eq15923 eq14839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14839 eq15923
  have eq17700 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17629 (σ x)
       grind)
    | exact superpose eq17629 eq16
    | exact resolve eq16 eq17629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17629
  have eq17710 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq17700
       have i₂ := eq15049 x
       grind)
    | exact superpose eq15049 eq17700
    | exact resolve eq17700 eq15049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15049 eq17700
  have eq17711 : False := by grind
  exact eq17711

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq22
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
  have eq72 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq90 x y
       grind)
    | exact superpose eq90 eq44
    | (have j1 := eq90 x y
       grind)
    | exact resolve eq44 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq116 eq90
    | (have j0 := eq90 (σ x) (σ y)
       grind)
    | exact resolve eq90 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq119
    | exact resolve eq119 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq123 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq120
       have r₂ := eq27
       grind)
    | exact resolve eq120 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq125 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq123
    | exact resolve eq123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq125 eq27
    | exact resolve eq27 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq125 eq73
    | (have r₁ := eq73
       have r₂ := eq125
       grind)
    | exact resolve eq73 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq125
  have eq464 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq463
  have eq467 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq464 eq116
    | exact resolve eq116 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq471 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq467
  have eq476 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq471
       have r₂ := eq127
       grind)
    | exact resolve eq471 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq471
  have eq481 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq476 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq476
       grind)
    | exact resolve eq13 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq512 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq481 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq624 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq512 eq116
    | exact resolve eq116 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq512
  have eq628 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq624
  have eq633 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq628
    | exact resolve eq628 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq635 : y = (M.op x y) := by
    first
    | (have r₁ := eq633
       have r₂ := eq27
       grind)
    | exact resolve eq633 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq637 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq635 eq20
    | exact resolve eq20 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq641 : y ≠ y ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq635 eq72
    | (have r₁ := eq72
       have r₂ := eq635
       grind)
    | exact resolve eq72 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq635
  have eq645 : y = (k x y) ∨ y = (M.op y y) := by grind
  clear eq641
  have eq651 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq637
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq637
    | exact resolve eq637 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq699 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq651 eq26
    | exact resolve eq26 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq827 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq645
       grind)
    | exact superpose eq645 eq44
    | exact resolve eq44 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq834 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq651 eq827
    | exact resolve eq827 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq836 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq834
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq834
    | exact resolve eq834 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq834
  have eq837 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq651 eq836
    | exact resolve eq836 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq840 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq837 eq90
    | (have j0 := eq90 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq90 eq837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq841 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by grind
  clear eq840
  have eq843 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq699 eq841
    | exact resolve eq841 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq846 : y = (M.op y y) := by
    first
    | (have r₁ := eq843
       have r₂ := eq27
       grind)
    | exact resolve eq843 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq851 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq846
       grind)
    | exact superpose eq846 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq846
       grind)
    | exact resolve eq13 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq875 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq851 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq914 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq875 x
       grind)
    | exact superpose eq875 eq44
    | exact resolve eq44 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq875
  have eq921 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq651 eq914
    | exact resolve eq914 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651 eq914
  have eq925 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq921
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq921
    | exact resolve eq921 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq921
  have eq928 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq925
    | exact resolve eq925 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq925
  have eq995 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq928 eq90
    | (have j0 := eq90 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq90 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq928
  have eq996 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq995
  have eq998 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq699 eq996
    | exact resolve eq996 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699 eq996
  have eq1001 : False := by grind
  exact eq1001

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation1724 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
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
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq75
    | exact resolve eq75 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
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
  have eq20101 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq77 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20102 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq20101
    | exact resolve eq20101 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20101
  have eq20113 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq20102
       have r₂ := eq28
       grind)
    | exact resolve eq20102 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20102
  have eq20117 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq20113
    | exact resolve eq20113 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20113
  have eq20120 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq20117 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq20117
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq20117
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq20117
       grind)
    | exact resolve eq12 eq20117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20117
  have eq20138 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq20120
  have eq20140 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq20138
       have r₂ := eq27
       grind)
    | exact resolve eq20138 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20138
  have eq20148 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq20140 eq77
    | exact resolve eq77 eq20140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq20140
  have eq20157 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq20148
  have eq20160 : (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq20157
       have r₂ := eq28
       grind)
    | exact resolve eq20157 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20157
  have eq20277 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq20160
       grind)
    | exact superpose eq20160 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq20160
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq20160
       grind)
    | exact resolve eq12 eq20160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20160
  have eq20295 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq20277
  have eq20297 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq20295
       have r₂ := eq19
       grind)
    | exact resolve eq20295 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20295
  have eq20301 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq49
       have i₂ := eq20297
       grind)
    | exact superpose eq20297 eq49
    | exact resolve eq49 eq20297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq20297
  have eq20317 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq20301
    | exact resolve eq20301 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20301
  have eq20466 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20317 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq20317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20467 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20466
  have eq20471 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq20467
    | exact resolve eq20467 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20467
  have eq20482 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq20471
       have r₂ := eq28
       grind)
    | exact resolve eq20471 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20471
  have eq20486 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq20482
    | exact resolve eq20482 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20482
  have eq20628 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20486 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq20486
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq20486
       grind)
    | exact resolve eq12 eq20486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20486
  have eq20646 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq20628
  have eq20648 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq20646
       have r₂ := eq27
       grind)
    | exact resolve eq20646 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20646
  have eq20664 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20648 eq20317
    | exact resolve eq20317 eq20648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20317 eq20648
  have eq20667 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq20664
  have eq20672 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq20667
       have r₂ := eq28
       grind)
    | exact resolve eq20667 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20667
  have eq20788 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq20672 eq30
    | exact resolve eq30 eq20672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq20672
  have eq20896 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq20788
    | exact resolve eq20788 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq20788
  have eq20897 : x = y := by grind
  clear eq20896
  have eq20916 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq20897
       grind)
    | exact superpose eq20897 eq19
    | exact resolve eq19 eq20897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq20917 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq20897
       grind)
    | exact superpose eq20897 eq25
    | exact resolve eq25 eq20897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq20897
  have eq21018 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq20917
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20917
    | exact resolve eq20917 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq20917
  have eq21033 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21018 eq27
    | exact resolve eq27 eq21018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq21018
  have eq21411 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq21033 eq68
    | exact resolve eq68 eq21033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq21033
  have eq21578 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq21411
       have i₂ := eq20916
       grind)
    | exact superpose eq20916 eq21411
    | exact resolve eq21411 eq20916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20916 eq21411
  have eq21591 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21578 eq15
    | exact resolve eq15 eq21578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21578
  have eq21637 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq21591
    | exact resolve eq21591 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq21591
  have eq21646 : False := by grind
  exact eq21646

/-- `Equation177`: `x = (y ◇ y) ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_pyy_x_pyx_pxy_Equation177 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law177 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law177.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0)
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op X0 X1)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = (k (M.op X1 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 X1) (M.op X0 X1)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X1 X1) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ X0 ∨ (k X1 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 (M.op X1 X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq12
    | (have j0 := eq12 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact resolve eq12 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq10
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq29
    | exact resolve eq29 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq32
    | (have j0 := eq32 (σ X0)
       grind)
    | exact resolve eq32 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq90 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (M.op X2 X1) = X1 ∨ (k X2 X1) = (M.op X1 X2) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 X1)) = X2 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 X0))) = X2 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq17 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 X1)) = X2 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq102 X0 X1
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq102
    | (have j0 := eq102 X0 X1
       grind)
    | exact resolve eq102 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq107 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (M.op X1 X1) (M.op X0 X1)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq18
    | exact resolve eq18 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op X1 (M.op X0 X0))
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq18
    | exact resolve eq18 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq18 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq111 X0 X1
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq111
    | exact resolve eq111 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq118 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq110 X0 X1
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq110
    | (have j0 := eq110 X0 X1
       grind)
    | exact resolve eq110 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq128 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 (M.op X0 X1) X1
       have i₂ := eq117 X1 X0
       grind)
    | exact superpose eq117 eq17
    | exact resolve eq17 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (k X1 (M.op (M.op X0 X1) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq117 X1 X0
       grind)
    | exact superpose eq117 eq12
    | (have j0 := eq12 X1 (M.op (M.op X0 X1) (M.op X0 X1))
       grind)
    | exact resolve eq12 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq128 (M.op X0 X0) X1
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq128
    | exact resolve eq128 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq105 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq105
    | (have j0 := eq105 (σ X1) (σ X0)
       grind)
    | exact resolve eq105 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq240 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) = (k (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq117 X0 X1
       grind)
    | exact superpose eq117 eq22
    | (have r₁ := eq22 (M.op X1 X1) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))
       have r₂ := eq117 (M.op X1 X1) X1
       grind)
    | exact resolve eq22 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq240 X0 X1
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq240
    | (have j0 := eq240 X0 X1
       grind)
    | (have r₁ := eq240 (M.op X0 X0) X0
       have r₂ := eq9 X0 X0
       grind)
    | (have r₁ := eq240 X0 (M.op (M.op X1 X1) (M.op (M.op X0 X0) X1))
       have r₂ := eq9 (M.op X0 X0) X1
       grind)
    | exact resolve eq240 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq333 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 (M.op X0 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1)
       have i₂ := eq107 X0 X1
       grind)
    | (have i₁ := eq9 X0 (M.op X1 X1)
       have i₂ := eq107 X1 X1
       grind)
    | exact superpose eq107 eq9
    | exact resolve eq9 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op (M.op X0 X0) (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 (M.op X0 X1) X2
       have i₂ := eq107 X0 X1
       grind)
    | (have i₁ := eq17 (M.op X1 X1) X1
       have i₂ := eq107 X1 X1
       grind)
    | exact superpose eq107 eq17
    | exact resolve eq17 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X0 X0)) = (M.op (M.op X2 X0) (M.op X2 X0)) ∨ (M.op X1 X2) = X2 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq92 X1 X2 (M.op (M.op X2 X0) (M.op X2 X0))
       have i₂ := eq18 X2 X0
       grind)
    | exact superpose eq18 eq92
    | (have j0 := eq92 X1 X2 X2
       grind)
    | exact resolve eq92 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X0) (M.op X2 X2)) ∨ (M.op X2 X1) = X1 ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 (M.op X0 X0) (M.op X2 X1)
       have i₂ := eq92 X0 X1 X2
       grind)
    | exact superpose eq92 eq18
    | (have j1 := eq92 X2 X1 X2
       grind)
    | exact resolve eq18 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq593 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X0 X0)) = (M.op (M.op X2 X0) (M.op X2 X0)) ∨ (M.op X2 X1) = X1 ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100 X1 X2 (M.op (M.op X2 X0) (M.op X2 X0))
       have i₂ := eq18 X2 X0
       grind)
    | exact superpose eq18 eq100
    | (have j0 := eq100 X1 X2 X2
       grind)
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X0) (M.op X2 X2)) ∨ (M.op X1 X2) = X2 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 (M.op X0 X0) (M.op X2 X1)
       have i₂ := eq100 X0 X1 X2
       grind)
    | exact superpose eq100 eq18
    | (have j1 := eq100 X2 X1 X2
       grind)
    | exact resolve eq18 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq643 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 (M.op X1 (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq333 X1 (M.op X0 X0) X2
       have i₂ := eq128 X0 X0
       grind)
    | exact superpose eq128 eq333
    | exact resolve eq333 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq688 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X1 X2)) X0) = (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq333 X1 X2 (M.op (M.op (M.op X1 X2) (M.op X1 X2)) X0)
       have i₂ := eq145 (M.op X1 X2) X0
       grind)
    | exact superpose eq145 eq333
    | exact resolve eq333 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq2094 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq247 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq2122 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op (M.op X0 X0) X0) = X0 ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq2094 (M.op X0 X0)
       have i₂ := eq100 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq100 eq2094
    | (have j1 := eq100 X0 (M.op X0 X0) x
       grind)
    | exact resolve eq2094 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq2094
  have eq2142 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = X0 ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq2122 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq2122
    | (have j0 := eq2122 X0
       grind)
    | exact resolve eq2122 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2122
  have eq2143 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq2142 X0
       have j1 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq2142 x
       have r₂ := eq12 (M.op x x) x
       grind)
    | exact resolve eq2142 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2142
  have eq2712 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq90 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq2713 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2712 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2712
  have eq2783 : ∀ X0 X1 : G, (M.op (σ (k X0 X0)) (M.op X1 (σ X0))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq9
    | (have j1 := eq71 X0
       grind)
    | exact resolve eq9 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq3666 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2713 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2713
  have eq4816 : ∀ X0 X1 : G, (M.op (σ (k (τ X0) (τ X0))) (M.op X1 X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2783 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2783
    | exact resolve eq2783 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2783
  have eq4865 : ∀ X0 X1 : G, (M.op (k X0 (σ (τ X0))) (M.op X1 X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4816 X0 X1
       have i₂ := eq24 X0 (τ X0)
       grind)
    | exact superpose eq24 eq4816
    | (have j0 := eq4816 X0 X1
       grind)
    | exact resolve eq4816 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4816
  have eq4880 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4865 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4865
    | (have j0 := eq4865 X0 X1
       grind)
    | exact resolve eq4865 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4865
  have eq5032 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op (M.op (M.op X0 X0) X1) X0) = X0 ∨ (M.op (M.op (M.op X0 X0) X1) X0) = (k (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq128 (M.op X0 X0) X1
       have i₂ := eq99 X0 (M.op (M.op X0 X0) X1) (M.op X0 X0)
       grind)
    | exact superpose eq99 eq128
    | (have j1 := eq99 X0 (M.op (M.op X0 X0) X1) x
       grind)
    | exact resolve eq128 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq5063 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op (M.op (M.op X0 X0) X1) X0) = (k (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5032 X0 X1
       have i₂ := eq145 X0 X1
       grind)
    | exact superpose eq145 eq5032
    | (have j0 := eq5032 X0 X1
       grind)
    | exact resolve eq5032 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5032
  have eq5106 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) X1) X0) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5063 X0 X1
       have i₂ := eq145 X0 X1
       grind)
    | exact superpose eq145 eq5063
    | (have j0 := eq5063 X0 X1
       grind)
    | exact resolve eq5063 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5063
  have eq5138 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op (k X1 X1) X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4880 X1 (M.op (M.op X1 X1) X0)
       have i₂ := eq145 X1 X0
       grind)
    | exact superpose eq145 eq4880
    | (have j0 := eq4880 X1 X1
       grind)
    | exact resolve eq4880 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5139 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (k (M.op X1 X1) (M.op X1 X1)) X0) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4880 (M.op X1 X1) (M.op X1 X0)
       have i₂ := eq128 X1 X0
       grind)
    | exact superpose eq128 eq4880
    | (have j0 := eq4880 (M.op X1 X1) X1
       grind)
    | exact resolve eq4880 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5167 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (k X0 X0) (k X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq108 (k X0 X0) X0
       have i₂ := eq4880 X0 X0
       grind)
    | exact superpose eq4880 eq108
    | (have j1 := eq4880 X0 x
       grind)
    | exact resolve eq108 eq4880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5169 : ∀ X0 X1 : G, (M.op (M.op (M.op (k X0 X0) (k X0 X0)) X0) (M.op X1 X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq643 X0 (k X0 X0) X1
       have i₂ := eq4880 X0 X0
       grind)
    | exact superpose eq4880 eq643
    | (have j1 := eq4880 X0 X1
       grind)
    | exact resolve eq643 eq4880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq5174 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = (k (M.op X1 X1) (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq338 X0 X1 (k (M.op X1 X1) (M.op X1 X1))
       have i₂ := eq4880 (M.op X1 X1) (M.op X0 X0)
       grind)
    | exact superpose eq4880 eq338
    | (have j1 := eq4880 (M.op X1 X1) X1
       grind)
    | exact resolve eq338 eq4880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5184 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op (k X1 X1) (k X1 X1))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq128 (k X1 X1) (M.op X0 X1)
       have i₂ := eq4880 X1 X0
       grind)
    | exact superpose eq4880 eq128
    | (have j1 := eq4880 X1 X1
       grind)
    | exact resolve eq128 eq4880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4880
  have eq5199 : ∀ X1 : G, (k (M.op X1 X1) (M.op X1 X1)) = X1 ∨ (M.op X1 X1) = (M.op (M.op X1 X1) (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq5174 x X1
       have i₂ := eq128 x X1
       grind)
    | exact superpose eq128 eq5174
    | (have j0 := eq5174 x X1
       grind)
    | exact resolve eq5174 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5174
  have eq5212 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (k (M.op X1 X1) (M.op X1 X1)) X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5139 X0 X1
       have i₂ := eq9 X1 X1
       grind)
    | exact superpose eq9 eq5139
    | (have j0 := eq5139 X0 X1
       grind)
    | exact resolve eq5139 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5139
  have eq5217 : ∀ X1 : G, (k (M.op X1 X1) (M.op X1 X1)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq5199 X1
       have i₂ := eq9 X1 X1
       grind)
    | exact superpose eq9 eq5199
    | (have j0 := eq5199 X1
       grind)
    | exact resolve eq5199 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5199
  have eq5758 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (k X0 X0)) (M.op X1 (k X0 X0))) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (k X0 X0)
       have i₂ := eq5138 (k X0 X0) X0
       grind)
    | exact superpose eq5138 eq9
    | (have j1 := eq5138 X0 X0
       grind)
    | exact resolve eq9 eq5138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5763 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 (M.op (M.op X0 X0) (k X0 X0)))) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 (k X0 X0) X1
       have i₂ := eq5138 (k X0 X0) X0
       grind)
    | exact superpose eq5138 eq17
    | (have j1 := eq5138 X0 X0
       grind)
    | exact resolve eq17 eq5138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5138
  have eq6029 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X1 ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5106 (M.op X0 X0) X1
       have i₂ := eq128 X0 X0
       grind)
    | exact superpose eq128 eq5106
    | (have j0 := eq5106 X0 X1
       grind)
    | exact resolve eq5106 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5106
  have eq7639 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X1) (σ X1)) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X1)
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq9
    | (have j1 := eq181 X0 X1
       grind)
    | exact resolve eq9 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq12815 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op (M.op X0 X1) (M.op X0 X1))) (M.op X2 (M.op (M.op X0 X1) (M.op X0 X1)))) = (M.op (M.op X2 X2) (M.op X1 X1)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq108 X0 (M.op X0 X0)
       have i₂ := eq452 X0 X0 X2
       grind)
    | (have i₁ := eq108 X0 (M.op X2 X0)
       have i₂ := eq452 X0 X1 X2
       grind)
    | exact superpose eq452 eq108
    | (have j1 := eq452 X0 X1 X0
       grind)
    | exact resolve eq108 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12996 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1))) (M.op X2 X1)) ∨ (M.op X0 X2) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq452 X0 X1 X2
       grind)
    | (have i₁ := eq18 (M.op X2 X0) (M.op X2 X0)
       have i₂ := eq452 X0 X1 X2
       grind)
    | exact superpose eq452 eq18
    | (have j1 := eq452 X0 X0 X2
       grind)
    | exact resolve eq18 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq452
  have eq13014 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) (M.op X2 X1)) ∨ (M.op X0 X2) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12996 X0 X1 X2
       have i₂ := eq108 (M.op X0 X0) X1
       grind)
    | exact superpose eq108 eq12996
    | (have j0 := eq12996 X0 X1 X2
       grind)
    | exact resolve eq12996 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12996
  have eq13054 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 X1)) = (M.op (M.op X2 X2) (M.op X1 X1)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12815 X0 X1 X2
       have i₂ := eq108 X2 (M.op X0 X1)
       grind)
    | exact superpose eq108 eq12815
    | (have j0 := eq12815 X0 X1 X2
       grind)
    | exact resolve eq12815 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12815
  have eq13166 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X0 X1) (M.op X2 X1)) ∨ (M.op X0 X2) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13014 X0 X1 X2
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq13014
    | (have j0 := eq13014 X0 X1 X2
       grind)
    | exact resolve eq13014 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13014
  have eq14637 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op X2 (M.op X0 X0)) (M.op X2 (M.op X0 X0))) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq107 X2 (M.op X0 X0)
       have i₂ := eq478 X0 X1 X0
       grind)
    | (have i₁ := eq107 X0 (M.op X0 X1)
       have i₂ := eq478 X0 X1 X2
       grind)
    | exact superpose eq478 eq107
    | (have j1 := eq478 X0 X1 X0
       grind)
    | exact resolve eq107 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq14725 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op X2 X2) X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14637 X0 X1 X2
       have i₂ := eq108 X2 X0
       grind)
    | exact superpose eq108 eq14637
    | (have j0 := eq14637 X0 X1 X2
       grind)
    | exact resolve eq14637 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq14637
  have eq17553 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X3 (M.op X2 X1))) = X3 ∨ (M.op X2 X0) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X2 X1)
       have i₂ := eq593 X1 X0 X2
       grind)
    | (have i₁ := eq9 X0 (M.op X0 X0)
       have i₂ := eq593 X0 X0 X2
       grind)
    | exact superpose eq593 eq9
    | (have j1 := eq593 X0 X0 X2
       grind)
    | exact resolve eq9 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq18607 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq620 X0 X1 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq620
    | (have j0 := eq620 X0 X1 X0
       grind)
    | exact resolve eq620 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq49477 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 (M.op (k X0 X0) (k X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k (M.op (k X0 X0) (k X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3666 (M.op (k X0 X0) (k X0 X0)) X0
       have i₂ := eq5167 X0
       grind)
    | exact superpose eq5167 eq3666
    | (have j0 := eq3666 X0 X0
       have j1 := eq5167 X0
       grind)
    | exact resolve eq3666 eq5167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5167
  have eq49672 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 (M.op (k X0 X0) (k X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k (M.op (k X0 X0) (k X0 X0)) X0) := by
    intro X0
    first
    | (have j0 := eq49477 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49477
  have eq49692 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (k X0 X0) (k X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq49672 X0
       have j1 := eq5184 X0 X0
       grind)
    | (have r₁ := eq49672 x
       have r₂ := eq5184 x x
       grind)
    | exact resolve eq49672 eq5184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5184 eq49672
  have eq49752 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 (k (M.op X0 X0) (M.op X0 X0))) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq49692 (M.op X0 X0)
       have i₂ := eq5212 (k (M.op X0 X0) (M.op X0 X0)) X0
       grind)
    | exact superpose eq5212 eq49692
    | (have j0 := eq49692 (M.op X0 X0)
       have j1 := eq5212 X0 (M.op X0 X0)
       grind)
    | exact resolve eq49692 eq5212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5212 eq49692
  have eq49875 : ∀ X0 : G, (k (M.op X0 (k (M.op X0 X0) (M.op X0 X0))) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq49752 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq49752
    | (have j0 := eq49752 X0
       grind)
    | exact resolve eq49752 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49752
  have eq49906 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (M.op X0 (k (M.op X0 X0) (M.op X0 X0))) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq49875 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq49875
    | (have j0 := eq49875 X0
       grind)
    | exact resolve eq49875 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49875
  have eq49907 : ∀ X0 : G, (k (M.op X0 (k (M.op X0 X0) (M.op X0 X0))) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq49906 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49906
  have eq89622 : ∀ X0 : G, (M.op (M.op (k X0 X0) (k X0 X0)) X0) ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 (M.op (M.op (k X0 X0) (k X0 X0)) X0) X0
       have i₂ := eq5169 X0 X0
       grind)
    | exact superpose eq5169 eq23
    | (have j1 := eq5169 X0 x
       grind)
    | (have r₁ := eq23 (M.op x x) x
       have r₂ := eq5169 (M.op x x) x
       grind)
    | exact resolve eq23 eq5169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq5169
  have eq89987 : ∀ X0 : G, (M.op (M.op (k X0 X0) (k X0 X0)) X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq89622 X0
       have j1 := eq12 (M.op (k X0 X0) (k X0 X0)) X0
       grind)
    | (have r₁ := eq89622 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq89622 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89622
  have eq116034 : ∀ X0 : G, (M.op (k X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5763 X0 (M.op (M.op X0 X0) (k X0 X0))
       have i₂ := eq5758 X0 (M.op X0 X0)
       grind)
    | exact superpose eq5758 eq5763
    | (have j0 := eq5763 X0 x
       have j1 := eq5758 X0 x
       grind)
    | exact resolve eq5763 eq5758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5758 eq5763
  have eq116177 : ∀ X0 : G, (M.op (k X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq116034 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116034
  have eq174342 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6029 X0 (k (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq49907 X0
       grind)
    | exact superpose eq49907 eq6029
    | (have j0 := eq6029 X0 X0
       have j1 := eq49907 X0
       grind)
    | exact resolve eq6029 eq49907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6029 eq49907
  have eq174379 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq174342 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174342
  have eq174427 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq174379 X0
       have j1 := eq22 X0 X0
       grind)
    | (have r₁ := eq174379 x
       have r₂ := eq22 x x
       grind)
    | exact resolve eq174379 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq174379
  have eq409292 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq174427 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174427
  have eq409370 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq409292 X0
       have j1 := eq5217 X0
       grind)
    | (have r₁ := eq409292 x
       have r₂ := eq5217 x
       grind)
    | exact resolve eq409292 eq5217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5217 eq409292
  have eq409899 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq409370 (M.op X0 X0)
       have i₂ := eq128 X0 X0
       grind)
    | exact superpose eq128 eq409370
    | exact resolve eq409370 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411375 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq409899 (σ X0)
       grind)
    | exact superpose eq409899 eq15
    | exact resolve eq15 eq409899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411391 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0 X0
       have i₂ := eq409899 (τ X0)
       grind)
    | exact superpose eq409899 eq41
    | exact resolve eq41 eq409899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411526 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq411391 X0
       have i₂ := eq409899 X0
       grind)
    | exact superpose eq409899 eq411391
    | exact resolve eq411391 eq409899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411391
  have eq411542 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq411375 X0
       have i₂ := eq409899 X0
       grind)
    | exact superpose eq409899 eq411375
    | exact resolve eq411375 eq409899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409899 eq411375
  have eq449941 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X1 X1)) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7639 X0 X1
       have i₂ := eq411542 X1
       grind)
    | exact superpose eq411542 eq7639
    | (have j0 := eq7639 X0 X1
       grind)
    | exact resolve eq7639 eq411542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7639
  have eq450250 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (M.op (τ X1) (τ X1))) (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq449941 (τ X0) (τ X1)
       have i₂ := eq41 X1 X0
       grind)
    | exact superpose eq41 eq449941
    | (have j0 := eq449941 (τ X0) (τ X1)
       grind)
    | exact resolve eq449941 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449941
  have eq450659 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (M.op (τ X1) (τ X1))) (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq450250 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq450250
    | (have j0 := eq450250 X0 X1
       grind)
    | exact resolve eq450250 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450250
  have eq451000 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ (M.op X1 X1))) (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq450659 X0 X1
       have i₂ := eq411526 X1
       grind)
    | exact superpose eq411526 eq450659
    | (have j0 := eq450659 X0 X1
       grind)
    | exact resolve eq450659 eq411526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411526 eq450659
  have eq451294 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op X1 X1) (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq451000 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq451000
    | (have j0 := eq451000 X0 X1
       grind)
    | exact resolve eq451000 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451000
  have eq451535 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (k X0 X1)) = X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq451294 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq451294
    | (have j0 := eq451294 X0 X1
       grind)
    | exact resolve eq451294 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451294
  have eq451732 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op (M.op X1 X1) (k X0 X1)) = X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq451535 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq451535
    | (have j0 := eq451535 X0 X1
       grind)
    | exact resolve eq451535 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451535
  have eq451884 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op (M.op X1 X1) (k X0 X1)) = X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq451732 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq451732
    | (have j0 := eq451732 X0 X1
       grind)
    | exact resolve eq451732 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451732
  have eq452007 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op (M.op X1 X1) (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq451884 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq451884
    | (have j0 := eq451884 X0 X1
       grind)
    | exact resolve eq451884 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451884
  have eq452062 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (k X0 X1)) = X0 ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq452007 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq452007
    | (have j0 := eq452007 X0 X1
       grind)
    | exact resolve eq452007 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452007
  have eq496364 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = (M.op (k X0 X1) (M.op X0 X0)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq117 (k X0 X1) (M.op X1 X1)
       have i₂ := eq452062 X0 X1
       grind)
    | exact superpose eq452062 eq117
    | (have j1 := eq452062 X0 X1
       grind)
    | exact resolve eq117 eq452062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452062
  have eq496622 : ∀ X0 X1 : G, (M.op (k X0 X1) (M.op X0 X0)) = X1 ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq496364 X0 X1
       have i₂ := eq9 X1 X1
       grind)
    | exact superpose eq9 eq496364
    | (have j0 := eq496364 X0 X1
       grind)
    | exact resolve eq496364 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496364
  have eq621852 : ∀ X0 X1 : G, (M.op (k (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X1 X0))) = (M.op (M.op (M.op X0 X0) (M.op X1 X0)) (k (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq116177 (M.op X1 X1)
       have i₂ := eq13054 X1 X1 X1
       grind)
    | (have i₁ := eq116177 (M.op X1 X1)
       have i₂ := eq13054 X0 X1 X1
       grind)
    | exact superpose eq13054 eq116177
    | (have j1 := eq13054 X1 X0 x
       grind)
    | exact resolve eq116177 eq13054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13054 eq116177
  have eq622452 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X0)) X0) = (M.op X0 (M.op (M.op X0 X0) (M.op X1 X0))) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq621852 X0 X1
       have i₂ := eq409370 X0
       grind)
    | exact superpose eq409370 eq621852
    | (have j0 := eq621852 X0 X1
       grind)
    | exact resolve eq621852 eq409370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621852
  have eq624289 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq622452 X1 X0
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq622452
    | (have j0 := eq622452 X0 X1
       grind)
    | exact resolve eq622452 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622452
  have eq625652 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq624289 X0 X1
       have j1 := eq3666 X0 X1
       grind)
    | (have r₁ := eq624289 X0 X1
       have r₂ := eq3666 X0 X1
       grind)
    | (have r₁ := eq624289 X1 X0
       have r₂ := eq3666 X0 X1
       grind)
    | exact resolve eq624289 eq3666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624289
  have eq626535 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq625652 X0 X1
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq625652
    | (have j0 := eq625652 X0 X1
       grind)
    | exact resolve eq625652 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625652
  have eq655514 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) (M.op X1 X0)) ∨ (k X0 (M.op (M.op X0 X0) (M.op X1 X0))) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq130 X1 X1
       have i₂ := eq13166 X1 X1 x
       grind)
    | (have i₁ := eq130 x X1
       have i₂ := eq13166 x X1 x
       grind)
    | exact superpose eq13166 eq130
    | (have j1 := eq13166 X0 X1 X1
       grind)
    | (have r₁ := eq130 X0 X0
       have r₂ := eq13166 (M.op X0 X0) X1 (M.op X0 X0)
       grind)
    | exact resolve eq130 eq13166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq655620 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op (k (M.op X0 X0) (M.op X0 X0)) X0) (M.op X1 X0)) ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (k (M.op X0 X0) (M.op X0 X0)) X1) = X1 ∨ (k (k (M.op X0 X0) (M.op X0 X0)) X1) = (M.op (k (M.op X0 X0) (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq89987 (M.op X0 X0)
       have i₂ := eq13166 (k (M.op X0 X0) (M.op X0 X0)) X0 X1
       grind)
    | exact superpose eq13166 eq89987
    | (have j0 := eq89987 (M.op X0 X0)
       have j1 := eq13166 (k (M.op X0 X0) (M.op X0 X0)) X1 X1
       grind)
    | (have r₁ := eq89987 x
       have r₂ := eq13166 (M.op (k x x) (k x x)) X1 x
       grind)
    | exact resolve eq89987 eq13166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13166 eq89987
  have eq658810 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) (M.op X1 X0)) ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (k (M.op X0 X0) (M.op X0 X0)) X1) = X1 ∨ (k (k (M.op X0 X0) (M.op X0 X0)) X1) = (M.op (k (M.op X0 X0) (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq655620 X0 X1
       have i₂ := eq409370 X0
       grind)
    | exact superpose eq409370 eq655620
    | (have j0 := eq655620 X0 X1
       grind)
    | exact resolve eq655620 eq409370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655620
  have eq658904 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 (M.op (M.op X0 X0) (M.op X1 X0))) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq655514 X0 X1
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq655514
    | (have j0 := eq655514 X0 X1
       grind)
    | (have r₁ := eq655514 X1 (M.op X1 X1)
       have r₂ := eq9 (M.op X1 X1) X1
       grind)
    | exact resolve eq655514 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655514
  have eq660888 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (k (M.op X0 X0) (M.op X0 X0)) X1) = X1 ∨ (k (k (M.op X0 X0) (M.op X0 X0)) X1) = (M.op (k (M.op X0 X0) (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq658810 X0 X1
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq658810
    | (have j0 := eq658810 X0 X1
       grind)
    | (have r₁ := eq658810 X1 (M.op X1 X1)
       have r₂ := eq9 (M.op X1 X1) X1
       grind)
    | exact resolve eq658810 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658810
  have eq660966 : ∀ X0 X1 : G, (k X0 (M.op (M.op X0 X0) (M.op X1 X0))) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq658904 X0 X1
       have j1 := eq626535 X0 X1
       grind)
    | (have r₁ := eq658904 X1 (k X1 X1)
       have r₂ := eq626535 X1 X1
       grind)
    | (have r₁ := eq658904 X1 X1
       have r₂ := eq626535 X1 X1
       grind)
    | (have r₁ := eq658904 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq626535 X0 (M.op X0 X0)
       grind)
    | exact resolve eq658904 eq626535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658904
  have eq662462 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op (k (M.op X0 X0) (M.op X0 X0)) X1) = X1 ∨ (k (k (M.op X0 X0) (M.op X0 X0)) X1) = (M.op (k (M.op X0 X0) (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq660888 X0 X1
       have i₂ := eq409370 X0
       grind)
    | exact superpose eq409370 eq660888
    | (have j0 := eq660888 X0 X1
       grind)
    | (have r₁ := eq660888 X0 (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0)))
       have r₂ := eq409370 (M.op X0 X0)
       grind)
    | exact resolve eq660888 eq409370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660888
  have eq662511 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq660966 X0 X1
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq660966
    | (have j0 := eq660966 X0 X1
       grind)
    | exact resolve eq660966 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660966
  have eq663356 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k (k (M.op X0 X0) (M.op X0 X0)) X1) = (M.op (k (M.op X0 X0) (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq662462 X0 X1
       have i₂ := eq409370 X0
       grind)
    | exact superpose eq409370 eq662462
    | (have j0 := eq662462 X0 X1
       grind)
    | (have r₁ := eq662462 X0 (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0)))
       have r₂ := eq409370 (M.op X0 X0)
       grind)
    | exact resolve eq662462 eq409370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662462
  have eq663401 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq662511 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq662511 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq662511 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662511
  have eq663955 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq663356 X0 X1
       have i₂ := eq409370 X0
       grind)
    | exact superpose eq409370 eq663356
    | (have j0 := eq663356 X0 X1
       grind)
    | (have r₁ := eq663356 X0 (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0)))
       have r₂ := eq409370 (M.op X0 X0)
       grind)
    | exact resolve eq663356 eq409370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409370 eq663356
  have eq664344 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq663955 X0 X1
       have j1 := eq626535 X0 X1
       grind)
    | (have r₁ := eq663955 X1 (k X1 X1)
       have r₂ := eq626535 X1 X1
       grind)
    | (have r₁ := eq663955 X1 X1
       have r₂ := eq626535 X1 X1
       grind)
    | (have r₁ := eq663955 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq626535 X0 (M.op X0 X0)
       grind)
    | exact resolve eq663955 eq626535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626535 eq663955
  have eq665092 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq663401 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq663401
    | exact resolve eq663401 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665597 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 X0
       have i₂ := eq663401 X0 (τ X1)
       grind)
    | exact superpose eq663401 eq25
    | (have j1 := eq663401 X0 (τ X1)
       grind)
    | exact resolve eq25 eq663401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq665945 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq663401 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663401
  have eq700849 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq665597 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq665597
    | exact resolve eq665597 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665597
  have eq701336 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq700849 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq700849
    | (have j0 := eq700849 X0 X1
       grind)
    | exact resolve eq700849 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700849
  have eq736996 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq665092 x y
       grind)
    | exact superpose eq665092 eq16
    | (have j1 := eq665092 x y
       grind)
    | exact resolve eq16 eq665092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq737655 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (σ X0) (σ X0))) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq128 (σ X0) (σ X1)
       have i₂ := eq665092 X0 X1
       grind)
    | exact superpose eq665092 eq128
    | (have j1 := eq665092 X0 X1
       grind)
    | exact resolve eq128 eq665092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665092
  have eq738034 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq737655 X0 X1
       have i₂ := eq411542 X0
       grind)
    | exact superpose eq411542 eq737655
    | (have j0 := eq737655 X0 X1
       grind)
    | exact resolve eq737655 eq411542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737655
  have eq753124 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq736996
       have i₂ := eq701336 y x
       grind)
    | exact superpose eq701336 eq736996
    | (have j1 := eq701336 y x
       grind)
    | (have r₁ := eq736996
       have r₂ := eq701336 y x
       grind)
    | exact resolve eq736996 eq701336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701336
  have eq753127 : (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by grind
  clear eq753124
  have eq753143 : (M.op x y) = (τ (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq753127
       grind)
    | exact superpose eq753127 eq10
    | exact resolve eq10 eq753127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753127
  have eq753343 : x = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq753143
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq753143
    | exact resolve eq753143 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753143
  have eq753364 : x = (k x y) := by
    first
    | (have j1 := eq665945 x y
       grind)
    | (have r₁ := eq753343
       have r₂ := eq665945 x y
       grind)
    | exact resolve eq753343 eq665945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665945 eq753343
  have eq763995 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq753364
       have i₂ := eq118 x y
       grind)
    | exact superpose eq118 eq753364
    | (have j1 := eq118 x y
       grind)
    | exact resolve eq753364 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq794879 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq664344 x y
       have i₂ := eq753364
       grind)
    | exact superpose eq753364 eq664344
    | (have j0 := eq664344 x y
       grind)
    | exact resolve eq664344 eq753364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664344
  have eq847182 : x ≠ (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq763995
  have eq847186 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq847182
       have r₂ := eq794879
       grind)
    | exact resolve eq847182 eq794879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794879 eq847182
  have eq847317 : (M.op y y) = (M.op (M.op x x) (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq107 x y
       have i₂ := eq847186
       grind)
    | exact superpose eq847186 eq107
    | exact resolve eq107 eq847186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq847186
  have eq855221 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq338 x y X0
       have i₂ := eq847317
       grind)
    | exact superpose eq847317 eq338
    | exact resolve eq338 eq847317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq904370 : (M.op x x) = (M.op (M.op x y) (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq855221 (M.op x x)
       have i₂ := eq847317
       grind)
    | exact superpose eq847317 eq855221
    | exact resolve eq855221 eq847317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847317 eq855221
  have eq904826 : (M.op x x) = (M.op (M.op x y) (M.op y y)) ∨ x = (M.op x y) := by grind
  clear eq904370
  have eq967547 : (M.op x y) = (M.op (M.op x x) (M.op x x)) ∨ (M.op x y) = (M.op (M.op y y) (M.op x y)) ∨ (M.op (M.op y y) (M.op x y)) = (k (M.op y y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18607 (M.op x y) (M.op y y)
       have i₂ := eq904826
       grind)
    | exact superpose eq904826 eq18607
    | (have j0 := eq18607 (M.op x y) (M.op y y)
       grind)
    | exact resolve eq18607 eq904826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18607 eq904826
  have eq967652 : x = (M.op x y) ∨ (M.op x y) = (M.op (M.op y y) (M.op x y)) ∨ (M.op (M.op y y) (M.op x y)) = (k (M.op y y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq967547
       have i₂ := eq9 x x
       grind)
    | exact superpose eq9 eq967547
    | exact resolve eq967547 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967547
  have eq967653 : x = (M.op x y) ∨ (M.op x y) = (M.op (M.op y y) (M.op x y)) ∨ (M.op (M.op y y) (M.op x y)) = (k (M.op y y) (M.op x y)) := by grind
  clear eq967652
  have eq967841 : x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op (M.op y y) (M.op x y)) = (k (M.op y y) (M.op x y)) := by
    first
    | (have i₁ := eq967653
       have i₂ := eq9 x y
       grind)
    | exact superpose eq9 eq967653
    | exact resolve eq967653 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967653
  have eq967842 : x = (M.op x y) ∨ (M.op (M.op y y) (M.op x y)) = (k (M.op y y) (M.op x y)) := by grind
  clear eq967841
  have eq967976 : x = (k (M.op y y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq967842
       have i₂ := eq9 x y
       grind)
    | exact superpose eq9 eq967842
    | exact resolve eq967842 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967842
  have eq1132293 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17553 X0 X0 X1 (M.op X1 X0)
       have i₂ := eq14725 X1 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14725 eq17553
    | (have j0 := eq17553 X0 X1 X1 x
       have j1 := eq14725 X1 X0 x
       grind)
    | exact resolve eq17553 eq14725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14725 eq17553
  have eq1133442 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1132293 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132293
  have eq1134503 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1133442 X0 X1
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq1133442
    | (have j0 := eq1133442 X0 X1
       grind)
    | exact resolve eq1133442 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133442
  have eq1135620 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1134503 X0 X1
       have j1 := eq3666 X1 X0
       grind)
    | (have r₁ := eq1134503 X0 X1
       have r₂ := eq3666 X0 X1
       grind)
    | (have r₁ := eq1134503 X1 X0
       have r₂ := eq3666 X0 X1
       grind)
    | exact resolve eq1134503 eq3666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3666 eq1134503
  have eq1137122 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1135620 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1135620
    | (have j0 := eq1135620 (σ X1) (σ X0)
       grind)
    | exact resolve eq1135620 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1137625 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq1135620 (σ X1) X0
       grind)
    | exact superpose eq1135620 eq29
    | (have j1 := eq1135620 (σ X1) X0
       grind)
    | exact resolve eq29 eq1135620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1138020 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq736996
       have i₂ := eq1135620 y x
       grind)
    | exact superpose eq1135620 eq736996
    | (have j1 := eq1135620 y x
       grind)
    | exact resolve eq736996 eq1135620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736996 eq1135620
  have eq1138032 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq1138020
  have eq1321292 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1137122 x y
       grind)
    | exact superpose eq1137122 eq16
    | (have j1 := eq1137122 x y
       grind)
    | exact resolve eq16 eq1137122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1322309 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1137122 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137122
  have eq1323010 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1321292
       have i₂ := eq753364
       grind)
    | exact superpose eq753364 eq1321292
    | exact resolve eq1321292 eq753364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321292
  have eq1325101 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1322309 (τ X0) (τ X1)
       have i₂ := eq41 X1 X0
       grind)
    | exact superpose eq41 eq1322309
    | (have j0 := eq1322309 (τ X0) (τ X1)
       grind)
    | exact resolve eq1322309 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1322309
  have eq1325348 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1325101 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1325101
    | (have j0 := eq1325101 X0 X1
       grind)
    | exact resolve eq1325101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325101
  have eq1325538 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1325348 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1325348
    | (have j0 := eq1325348 X0 X1
       grind)
    | exact resolve eq1325348 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325348
  have eq1325696 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1325538 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1325538
    | (have j0 := eq1325538 X0 X1
       grind)
    | exact resolve eq1325538 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325538
  have eq1325809 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1325696 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1325696
    | (have j0 := eq1325696 X0 X1
       grind)
    | exact resolve eq1325696 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325696
  have eq1326231 : x ≠ y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1325809 x y
       have i₂ := eq753364
       grind)
    | exact superpose eq753364 eq1325809
    | (have j0 := eq1325809 x y
       grind)
    | exact resolve eq1325809 eq753364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753364 eq1325809
  have eq1326532 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1323010
       have i₂ := eq1138032
       grind)
    | exact superpose eq1138032 eq1323010
    | (have r₁ := eq1323010
       have r₂ := eq1138032
       grind)
    | exact resolve eq1323010 eq1138032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323010
  have eq1326534 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1326532
  have eq1326553 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1326534
       grind)
    | exact superpose eq1326534 eq16
    | exact resolve eq16 eq1326534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1326580 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9 (σ x) (σ y)
       have i₂ := eq1326534
       grind)
    | exact superpose eq1326534 eq9
    | exact resolve eq9 eq1326534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326534
  have eq1326864 : (σ x) = (M.op (σ (M.op y y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1326580
       have i₂ := eq411542 y
       grind)
    | exact superpose eq411542 eq1326580
    | exact resolve eq1326580 eq411542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326580
  have eq1327173 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1326553
       have i₂ := eq1138032
       grind)
    | exact superpose eq1138032 eq1326553
    | exact resolve eq1326553 eq1138032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138032 eq1326553
  have eq1327176 : (σ x) ≠ (σ y) ∨ y = (M.op x y) := by grind
  clear eq1327173
  have eq1330879 : (τ (σ x)) = (k (τ (σ (M.op y y))) y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1137625 (σ (M.op y y)) y
       have i₂ := eq1326864
       grind)
    | exact superpose eq1326864 eq1137625
    | exact resolve eq1137625 eq1326864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137625 eq1326864
  have eq1331170 : (τ (σ x)) = (k (τ (σ (M.op y y))) y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1330879
       have r₂ := eq1327176
       grind)
    | exact resolve eq1330879 eq1327176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327176 eq1330879
  have eq1331306 : (τ (σ x)) = (k (M.op y y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1331170
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq1331170
    | exact resolve eq1331170 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331170
  have eq1331409 : x = (k (M.op y y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1331306
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1331306
    | exact resolve eq1331306 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331306
  have eq1331598 : x = (M.op (M.op y y) y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2143 y
       have i₂ := eq1331409
       grind)
    | exact superpose eq1331409 eq2143
    | exact resolve eq2143 eq1331409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143
  have eq1331643 : y = (M.op x (M.op (M.op y y) (M.op y y))) ∨ y = (M.op (M.op y y) y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq496622 (M.op y y) y
       have i₂ := eq1331409
       grind)
    | exact superpose eq1331409 eq496622
    | (have j0 := eq496622 (M.op y y) y
       grind)
    | exact resolve eq496622 eq1331409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496622 eq1331409
  have eq1331673 : y = (M.op x y) ∨ y = (M.op (M.op y y) y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1331643
       have i₂ := eq9 y y
       grind)
    | exact superpose eq9 eq1331643
    | exact resolve eq1331643 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331643
  have eq1331674 : y = (M.op (M.op y y) y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq1331673
  have eq1338879 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq145 y y
       have i₂ := eq1331598
       grind)
    | exact superpose eq1331598 eq145
    | exact resolve eq145 eq1331598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331598
  have eq1339110 : y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq1338879
  have eq1339417 : (M.op x x) = (M.op y (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq117 y x
       have i₂ := eq1339110
       grind)
    | exact superpose eq1339110 eq117
    | exact resolve eq117 eq1339110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339110
  have eq1341370 : ∀ X0 : G, (M.op (M.op (M.op x x) (M.op x x)) X0) = (M.op (M.op (M.op y y) (M.op (M.op y y) (M.op y y))) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq688 X0 y (M.op y y)
       have i₂ := eq1339417
       grind)
    | exact superpose eq1339417 eq688
    | exact resolve eq688 eq1339417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688 eq1339417
  have eq1341601 : ∀ X0 : G, (M.op (M.op (M.op y y) y) X0) = (M.op (M.op (M.op x x) (M.op x x)) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq1341370 X0
       have i₂ := eq9 y y
       grind)
    | exact superpose eq9 eq1341370
    | exact resolve eq1341370 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341370
  have eq1341709 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op y y) y) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq1341601 X0
       have i₂ := eq9 x x
       grind)
    | exact superpose eq9 eq1341601
    | exact resolve eq1341601 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341601
  have eq1367807 : (M.op (M.op y y) (M.op y y)) = (M.op y (M.op x (M.op (M.op y y) y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq117 y (M.op y y)
       have i₂ := eq1341709 (M.op (M.op y y) y)
       grind)
    | exact superpose eq1341709 eq117
    | exact resolve eq117 eq1341709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341709
  have eq1369922 : y = (M.op y (M.op x (M.op (M.op y y) y))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1367807
       have i₂ := eq9 y y
       grind)
    | exact superpose eq9 eq1367807
    | exact resolve eq1367807 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367807
  have eq1451582 : y = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq145 y y
       have i₂ := eq1331674
       grind)
    | exact superpose eq1331674 eq145
    | exact resolve eq145 eq1331674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq1331674
  have eq1451840 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq1451582
  have eq1452225 : y = (M.op y (M.op x (M.op y y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1369922
       have i₂ := eq1451840
       grind)
    | exact superpose eq1451840 eq1369922
    | exact resolve eq1369922 eq1451840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369922 eq1451840
  have eq1453235 : y = (M.op y (M.op x (M.op y y))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1452225
       have r₂ := eq1326231
       grind)
    | exact resolve eq1452225 eq1326231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452225
  have eq1453447 : x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1453235
       have i₂ := eq17 y x
       grind)
    | exact superpose eq17 eq1453235
    | exact resolve eq1453235 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1453235
  have eq1453465 : y = (M.op x y) := by
    first
    | (have r₁ := eq1453447
       have r₂ := eq1326231
       grind)
    | exact resolve eq1453447 eq1326231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326231 eq1453447
  have eq1453583 : y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq128 x y
       have i₂ := eq1453465
       grind)
    | exact superpose eq1453465 eq128
    | exact resolve eq128 eq1453465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq1793732 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op (M.op y y) (M.op y y)))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq738034 (M.op y y) (M.op x y)
       have i₂ := eq967976
       grind)
    | exact superpose eq967976 eq738034
    | exact resolve eq738034 eq967976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738034 eq967976
  have eq1794994 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1793732
       have i₂ := eq9 y y
       grind)
    | exact superpose eq9 eq1793732
    | exact resolve eq1793732 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1793732
  have eq1795557 : (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1794994
       have r₂ := eq16
       grind)
    | exact resolve eq1794994 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1794994
  have eq1795940 : (σ x) = (σ (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq1795557
       have i₂ := eq1453465
       grind)
    | exact superpose eq1453465 eq1795557
    | exact resolve eq1795557 eq1453465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1453465 eq1795557
  have eq1796591 : (M.op y y) = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1795940
       grind)
    | exact superpose eq1795940 eq10
    | exact resolve eq10 eq1795940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795940
  have eq1796856 : x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1796591
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1796591
    | exact resolve eq1796591 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796591
  have eq1797880 : x = (M.op y (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq117 y y
       have i₂ := eq1796856
       grind)
    | exact superpose eq1796856 eq117
    | exact resolve eq117 eq1796856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq1796856
  have eq1798418 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1797880
       have i₂ := eq1453583
       grind)
    | exact superpose eq1453583 eq1797880
    | exact resolve eq1797880 eq1453583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1453583 eq1797880
  have eq1798419 : x = y := by grind
  clear eq1798418
  have eq1799186 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1798419
       grind)
    | exact superpose eq1798419 eq16
    | exact resolve eq16 eq1798419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1798419
  have eq1799606 : False := by grind
  exact eq1799606

/-- `Equation177`: `x = (y ◇ y) ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_x_pyx_Equation177 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law177 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law177.models_iff G M).mp hM
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X1)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
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
  have eq35 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0)
       have i₂ := eq16 X0 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X1 X1) (M.op X0 X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : x = (M.op (M.op y y) (M.op x y)) := by
    first
    | (have i₁ := eq16 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq50 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq52 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq53 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq54 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq15
    | exact resolve eq15 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq50 eq15
    | exact resolve eq15 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq15
    | exact resolve eq15 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq60 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq60
    | (have j0 := eq60 y
       grind)
    | exact resolve eq60 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq60
    | (have j0 := eq60 (M.op x y)
       grind)
    | exact resolve eq60 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 X1)) X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 (M.op X1 (M.op X0 X0)) X0
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq28
    | exact resolve eq28 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X0
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (k X0 X1)) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq52 y
       have i₂ := eq156
       grind)
    | exact superpose eq156 eq52
    | exact resolve eq52 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq186 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq185
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq185
    | exact resolve eq185 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq188 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq186
    | exact resolve eq186 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq192 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq188 eq157
    | exact resolve eq157 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq192
       have r₂ := eq27
       grind)
    | exact resolve eq192 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq197 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq195 eq40
    | exact resolve eq40 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq198 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq195 eq39
    | exact resolve eq39 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq195 eq27
    | exact resolve eq27 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : (σ x) = (M.op (k (σ y) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq198
       have i₂ := eq28 sF3 sF3
       grind)
    | exact superpose eq28 eq198
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq198 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : (k (σ y) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq200 eq16
    | exact resolve eq16 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (k (σ y) (σ y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq212 eq16
    | exact resolve eq16 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq234 : (M.op (σ x) (σ x)) = (M.op (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq226 eq16
    | exact resolve eq16 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq256 : (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq234 eq35
    | exact resolve eq35 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq260 : (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) = (k (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq256
       have i₂ := eq149 sF2
       grind)
    | exact superpose eq149 eq256
    | exact resolve eq256 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq269 : ∀ X0 : G, (k (M.op (σ x) (σ x)) (σ x)) ≠ X0 ∨ (k X0 (k (σ y) (σ y))) = (M.op (k (σ y) (σ y)) X0) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq260 eq13
    | (have j0 := eq13 X0 (k (σ y) (σ y))
       grind)
    | (have r₁ := eq13 (k (M.op (σ x) (σ x)) (σ x)) (k (σ y) (σ y))
       have r₂ := eq260
       grind)
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq260
       grind)
    | exact resolve eq13 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 : G, (M.op (k (σ y) (σ y)) (M.op X0 (k (M.op (σ x) (σ x)) (σ x)))) = X0 ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq260 eq35
    | exact resolve eq35 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq348 : x ≠ (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) := by
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
  have eq349 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq425 : (k (k (M.op (σ x) (σ x)) (σ x)) (k (σ y) (σ y))) = (M.op (k (σ y) (σ y)) (k (M.op (σ x) (σ x)) (σ x))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have j0 := eq269 (k (M.op (σ x) (σ x)) (σ x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq487 : (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (k (k (M.op (σ x) (σ x)) (σ x)) (k (σ y) (σ y)))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq425 eq270
    | exact resolve eq270 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq490 : (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (k (k (M.op (σ x) (σ x)) (σ x)) (k (σ y) (σ y)))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq487
  have eq626 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq51 X1 X0
       grind)
    | exact superpose eq51 eq15
    | exact resolve eq15 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq933 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq149 (M.op X0 X0)
       have i₂ := eq16 X0 X0
       grind)
    | exact superpose eq16 eq149
    | exact resolve eq149 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq946 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq36 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq36
    | exact resolve eq36 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq958 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq197 eq36
    | exact resolve eq36 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq995 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq16
    | exact resolve eq16 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq996 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X1 X1) X0))
       have i₂ := eq36 (M.op X1 X1) X0
       grind)
    | exact superpose eq36 eq35
    | exact resolve eq35 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1025 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ y) (σ y)) (σ x)) (M.op (M.op (σ y) (σ y)) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq958
       have i₂ := eq995 sF2 (M.op sF3 sF3)
       grind)
    | exact superpose eq995 eq958
    | exact resolve eq958 eq995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958 eq995
  have eq1034 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq946 X0 X1
       have i₂ := eq16 X0 X0
       grind)
    | exact superpose eq16 eq946
    | exact resolve eq946 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq1048 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1025
       have i₂ := eq996 sF2 sF3
       grind)
    | exact superpose eq996 eq1025
    | exact resolve eq1025 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996 eq1025
  have eq1067 : (σ y) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1048 eq35
    | exact resolve eq35 eq1048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq1075 : (σ y) = (k (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1067
       have i₂ := eq149 sF2
       grind)
    | exact superpose eq149 eq1067
    | exact resolve eq1067 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067
  have eq1093 : (k (σ y) (k (σ y) (σ y))) = (M.op (k (σ y) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1075 eq425
    | exact resolve eq425 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq1094 : (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (k (σ y) (k (σ y) (σ y)))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1075 eq490
    | exact resolve eq490 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq1104 : (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (k (σ y) (k (σ y) (σ y)))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1094
  have eq1105 : (k (σ y) (k (σ y) (σ y))) = (M.op (k (σ y) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1093
  have eq1451 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq195 eq349
    | (have r₁ := eq349
       have r₂ := eq195
       grind)
    | exact resolve eq349 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq349
  have eq1452 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1451
  have eq1453 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq188 eq1452
    | exact resolve eq1452 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452
  have eq1486 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1453 eq1075
    | exact resolve eq1075 eq1453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075 eq1453
  have eq1502 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1486
  have eq1981 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1502 eq188
    | exact resolve eq188 eq1502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1502
  have eq1987 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1981
  have eq1993 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1987 eq29
    | exact resolve eq29 eq1987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1994 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ y) (σ X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1987 eq63
    | exact resolve eq63 eq1987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq1996 : (k y (M.op x y)) = (τ (k (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1987 eq129
    | exact resolve eq129 eq1987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq1999 : (k y y) = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128 eq1996
    | exact resolve eq1996 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1996
  have eq2001 : ∀ X0 : G, (k y X0) = (k (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq60 eq1994
    | exact resolve eq1994 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq1994
  have eq2002 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq1993
    | exact resolve eq1993 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1993
  have eq2008 : x = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37
       have i₂ := eq2002
       grind)
    | exact superpose eq2002 eq37
    | exact resolve eq37 eq2002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2015 : x = (k (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2008
       have i₂ := eq933 sF0
       grind)
    | exact superpose eq933 eq2008
    | exact resolve eq2008 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2008
  have eq2101 : (σ x) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2015 eq50
    | exact resolve eq50 eq2015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq2104 : (σ x) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2101
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2101
    | exact resolve eq2101 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2101
  have eq2106 : (σ x) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1987 eq2104
    | exact resolve eq2104 eq1987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2104
  have eq2297 : (σ x) = (k (σ y) (σ (k (M.op x y) (M.op x y)))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq2106
       have i₂ := eq28 sF0 sF0
       grind)
    | exact superpose eq28 eq2106
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq2106 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2106
  have eq2305 : (σ x) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq54 eq2297
    | exact resolve eq2297 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq2297
  have eq2308 : (σ x) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq2305
    | exact resolve eq2305 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2305
  have eq2309 : (σ x) = (k (σ y) (k (σ y) (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1987 eq2308
    | exact resolve eq2308 eq1987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1987 eq2308
  have eq2899 : (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2309 eq1104
    | exact resolve eq1104 eq2309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq2901 : (σ x) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2309 eq175
    | (have j0 := eq175 (k (σ y) (σ y)) (σ y)
       grind)
    | exact resolve eq175 eq2309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2903 : (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq2899
  have eq2908 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq200 eq2903
    | exact resolve eq2903 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq2903
  have eq2990 : (k (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2309 eq161
    | (have j0 := eq161 (σ y) (k (σ y) (σ y))
       grind)
    | exact resolve eq161 eq2309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2309
  have eq3034 : (σ x) = (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq198 eq2990
    | exact resolve eq2990 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq2990
  have eq3081 : (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq3034
       have r₂ := eq2901
       grind)
    | exact resolve eq3034 eq2901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2901 eq3034
  have eq3273 : (k (σ y) (σ y)) = (k (σ y) (k (σ y) (σ y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3081 eq1105
    | exact resolve eq1105 eq3081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105 eq3081
  have eq3282 : (k (σ y) (σ y)) = (k (σ y) (k (σ y) (σ y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq3273
  have eq3289 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2908 eq3282
    | exact resolve eq3282 eq2908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2908 eq3282
  have eq3292 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq188 eq3289
    | exact resolve eq3289 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq3289
  have eq3293 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq3292
       have r₂ := eq199
       grind)
    | exact resolve eq3292 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq3292
  have eq3310 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3293 eq149
    | exact resolve eq149 eq3293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3327 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3293 eq3310
    | exact resolve eq3310 eq3293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3293 eq3310
  have eq3351 : (τ (σ y)) = (k y y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3327 eq128
    | exact resolve eq128 eq3327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3327
  have eq3469 : y = (k y y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq32 eq3351
    | exact resolve eq3351 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3351
  have eq3470 : y = (k y (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1999 eq3469
    | exact resolve eq3469 eq1999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1999 eq3469
  have eq3471 : y = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2001 eq3470
    | exact resolve eq3470 eq2001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2001 eq3470
  have eq3472 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2002 eq3471
    | exact resolve eq3471 eq2002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2002 eq3471
  have eq3473 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq175 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq3472
       have r₂ := eq175 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq3472 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3472
  have eq3477 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3473 eq2015
    | exact resolve eq2015 eq3473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2015
  have eq3482 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3473 eq149
    | exact resolve eq149 eq3473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3489 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq3477
  have eq3493 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3473 eq3482
    | exact resolve eq3482 eq3473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3473 eq3482
  have eq3529 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3493 eq3489
    | exact resolve eq3489 eq3493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3489 eq3493
  have eq3536 : x = (M.op x y) := by grind
  clear eq3529
  have eq3547 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3536
       grind)
    | exact superpose eq3536 eq18
    | exact resolve eq18 eq3536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3548 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq3536
       grind)
    | exact superpose eq3536 eq22
    | exact resolve eq22 eq3536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq3551 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq52 X0
       have i₂ := eq3536
       grind)
    | exact superpose eq3536 eq52
    | exact resolve eq52 eq3536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq3552 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ y = (k y (M.op x y)) := by
    first
    | (have i₁ := eq348
       have i₂ := eq3536
       grind)
    | exact superpose eq3536 eq348
    | (have r₁ := eq348
       have r₂ := eq3536
       grind)
    | exact resolve eq348 eq3536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq3553 : y = (k y (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq3552
  have eq3556 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3548 eq20
    | exact resolve eq20 eq3548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3548
  have eq3959 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3553 eq3551
    | exact resolve eq3551 eq3553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3553
  have eq3964 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq3959
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3959
    | exact resolve eq3959 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3959
  have eq3975 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3964 eq157
    | exact resolve eq157 eq3964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3964
  have eq4096 : (k y (M.op x y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3975 eq149
    | exact resolve eq149 eq3975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq3975
  have eq4108 : (M.op x y) = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3547 eq4096
    | exact resolve eq4096 eq3547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3547 eq4096
  have eq4192 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4108 eq49
    | exact resolve eq49 eq4108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq4108
  have eq4202 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq4192
    | exact resolve eq4192 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4192
  have eq4205 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3556 eq4202
    | exact resolve eq4202 eq3556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4202
  have eq4335 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4205 eq157
    | exact resolve eq157 eq4205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq4205
  have eq4346 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4335
  have eq4375 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
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
  have eq4406 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq4375 X0
       have i₂ := eq3536
       grind)
    | exact superpose eq3536 eq4375
    | exact resolve eq4375 eq3536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4375
  have eq4419 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4346 eq39
    | exact resolve eq39 eq4346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq4423 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4346
  have eq4425 : (σ x) = (k (σ y) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4419
       have i₂ := eq933 sF3
       grind)
    | exact superpose eq933 eq4419
    | exact resolve eq4419 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4419
  have eq4517 : (σ x) = (k (σ y) (k (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4425
       have i₂ := eq28 sF3 sF3
       grind)
    | exact superpose eq28 eq4425
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq4425 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq7863 : ∀ X0 X1 : G, (k (k X0 (M.op x y)) (τ X1)) = (τ (k (k (σ X0) (σ x)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq3551 eq626
    | exact resolve eq626 eq3551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626 eq3551
  have eq8592 : ∀ X0 X1 : G, (τ (k (k X0 (σ x)) X1)) = (k (k (τ X0) (M.op x y)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7863 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq7863
    | exact resolve eq7863 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7863
  have eq8832 : ∀ X0 : G, (τ (k (k X0 (σ x)) (k (σ y) (σ y)))) = (k (k (τ X0) (M.op x y)) (k y y)) := by
    intro X0
    first
    | exact superpose eq128 eq8592
    | exact resolve eq8592 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq8592
  have eq9192 : ∀ X0 : G, (τ X0) = (k (τ (M.op X0 (M.op (σ x) (σ x)))) (M.op x y)) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq4406 (M.op X0 (M.op sF2 sF2))
       have i₂ := eq150 X0 sF2
       grind)
    | exact superpose eq150 eq4406
    | (have j1 := eq150 (τ X0) (k (τ (M.op X0 (M.op (σ x) (σ x)))) (M.op x y))
       grind)
    | exact resolve eq4406 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4406
  have eq13253 : ∀ X0 : G, (τ (k X0 (k (σ y) (σ y)))) = (k (k (τ (M.op X0 (M.op (σ x) (σ x)))) (M.op x y)) (k y y)) ∨ (σ x) = X0 := by
    intro X0
    first
    | (have i₁ := eq8832 (M.op X0 (M.op sF2 sF2))
       have i₂ := eq150 X0 sF2
       grind)
    | exact superpose eq150 eq8832
    | (have j1 := eq150 (τ (k X0 (k (σ y) (σ y)))) (k (k (τ (M.op X0 (M.op (σ x) (σ x)))) (M.op x y)) (k y y))
       grind)
    | exact resolve eq8832 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq8832
  have eq13328 : ∀ X0 : G, (τ (k X0 (k (σ y) (σ y)))) = (k (τ X0) (k y y)) ∨ (σ x) = X0 := by
    intro X0
    first
    | exact superpose eq9192 eq13253
    | (have j0 := eq13253 X0
       have j1 := eq9192 X0
       grind)
    | exact resolve eq13253 eq9192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9192 eq13253
  have eq13372 : (τ (σ x)) = (k (τ (σ y)) (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq4517 eq13328
    | (have j0 := eq13328 (σ y)
       grind)
    | exact resolve eq13328 eq4517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4517 eq13328
  have eq13426 : (τ (σ x)) = (k (τ (σ y)) (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq13372
       have r₂ := eq4423
       grind)
    | exact resolve eq13372 eq4423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13372
  have eq13441 : (τ (σ x)) = (k y (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq32 eq13426
    | exact resolve eq13426 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq13426
  have eq13445 : x = (k y (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq30 eq13441
    | exact resolve eq13441 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq13441
  have eq13447 : (M.op x y) = (k y (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq13445
       have i₂ := eq3536
       grind)
    | exact superpose eq3536 eq13445
    | exact resolve eq13445 eq3536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13445
  have eq13499 : ∀ X0 X1 : G, (M.op (k X1 X1) (k X1 X1)) = (M.op (M.op X0 X1) (M.op X0 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1034 (M.op X1 X0) (k X0 X0)
       have i₂ := eq160 X0 X1
       grind)
    | exact superpose eq160 eq1034
    | (have j1 := eq160 X1 X1
       grind)
    | exact resolve eq1034 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13597 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35 (M.op X0 X1) X1
       have i₂ := eq1034 X1 X0
       grind)
    | exact superpose eq1034 eq35
    | exact resolve eq35 eq1034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1034
  have eq13617 : ∀ X1 : G, (M.op (k X1 X1) (k X1 X1)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq13499 x X1
       have i₂ := eq13597 x X1
       grind)
    | exact superpose eq13597 eq13499
    | (have j0 := eq13499 x X1
       grind)
    | exact resolve eq13499 eq13597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13499 eq13597
  have eq13693 : (M.op (M.op y y) (M.op x y)) = (k y y) ∨ (k y y) = (M.op (k y y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq161 y (k y y)
       have i₂ := eq13447
       grind)
    | exact superpose eq13447 eq161
    | (have j0 := eq161 y (k y y)
       grind)
    | exact resolve eq161 eq13447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq13694 : (M.op x y) ≠ (k y y) ∨ (k y y) = (M.op (k y y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq175 (k y y) y
       have i₂ := eq13447
       grind)
    | exact superpose eq13447 eq175
    | (have j0 := eq175 (k y y) y
       grind)
    | exact resolve eq175 eq13447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13447
  have eq13696 : x = (k y y) ∨ (k y y) = (M.op (k y y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq37 eq13693
    | exact resolve eq13693 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq13693
  have eq13699 : (M.op x y) = (k y y) ∨ (k y y) = (M.op (k y y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq13696
       have i₂ := eq3536
       grind)
    | exact superpose eq3536 eq13696
    | exact resolve eq13696 eq3536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3536 eq13696
  have eq13702 : (k y y) = (M.op (k y y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq13699
       have r₂ := eq13694
       grind)
    | exact resolve eq13699 eq13694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13694 eq13699
  have eq14508 : (k y y) = (M.op (k y y) (k y y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq160 y (k y y)
       have i₂ := eq13702
       grind)
    | exact superpose eq13702 eq160
    | (have j0 := eq160 (k y y) x
       grind)
    | exact resolve eq160 eq13702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq13702
  have eq14513 : y = (k y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq13617 eq14508
    | (have j1 := eq13617 y
       grind)
    | exact resolve eq14508 eq13617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13617 eq14508
  have eq14517 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq175 (σ y) (σ y)
       grind)
    | (have r₁ := eq14513
       have r₂ := eq175 y y
       grind)
    | exact resolve eq14513 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14513
  have eq14559 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq14517 eq36
    | exact resolve eq36 eq14517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14517
  have eq14572 : (σ y) = (k (σ y) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14559
       have i₂ := eq933 sF3
       grind)
    | exact superpose eq933 eq14559
    | exact resolve eq14559 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14559
  have eq14582 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4425 eq14572
    | exact resolve eq14572 eq4425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14572
  have eq14587 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq14582
       have r₂ := eq4423
       grind)
    | exact resolve eq14582 eq4423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14582
  have eq14620 : (M.op y y) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq933 y
       have i₂ := eq14587
       grind)
    | exact superpose eq14587 eq933
    | exact resolve eq933 eq14587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14631 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14587 eq14620
    | exact resolve eq14620 eq14587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14587 eq14620
  have eq14692 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53 y
       have i₂ := eq14631
       grind)
    | exact superpose eq14631 eq53
    | exact resolve eq53 eq14631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq14631
  have eq14706 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14692
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14692
    | exact resolve eq14692 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq14692
  have eq14797 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14706 eq175
    | (have j0 := eq175 (σ y) (σ y)
       grind)
    | (have r₁ := eq175 (σ y) (σ y)
       have r₂ := eq14706
       grind)
    | exact resolve eq175 eq14706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq14706
  have eq14798 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14797
  have eq14875 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14798 eq36
    | exact resolve eq36 eq14798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq14798
  have eq14888 : (σ y) = (k (σ y) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14875
       have i₂ := eq933 sF3
       grind)
    | exact superpose eq933 eq14875
    | exact resolve eq14875 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933 eq14875
  have eq14898 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4425 eq14888
    | exact resolve eq14888 eq4425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4425 eq14888
  have eq14900 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq14898
       have r₂ := eq4423
       grind)
    | exact resolve eq14898 eq4423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4423 eq14898
  have eq14904 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq14900 eq27
    | exact resolve eq27 eq14900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq14900
  have eq14913 : False := by grind
  exact eq14913
