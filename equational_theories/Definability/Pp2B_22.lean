import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_x_pyy_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq61 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
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
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : ∀ X1 : G, (M.op X1 X1) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq78 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq115
    | exact resolve eq115 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq155 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq329 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq363 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3 X4
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq62
    | exact resolve eq62 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) (M.op X0 X5)) X0) = X0 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq62 X0 (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X4 X5
       have i₂ := eq62 X0 X1 X2 X3
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq62 X0 X1 X2 X3
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X1)) (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq60 eq62
    | exact resolve eq62 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq374 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq61 eq62
    | exact resolve eq62 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq62
    | (have j0 := eq62 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq62 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq62 X0 X1 X2 X3
       grind)
    | exact superpose eq62 eq14
    | exact resolve eq14 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq383 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq383
    | exact resolve eq383 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq386 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq374
    | (have j0 := eq374 X0 X1
       grind)
    | exact resolve eq374 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq387 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X1)) (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq373 X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq373
    | (have j0 := eq373 X0 X1
       grind)
    | exact resolve eq373 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq388 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq372 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq372
    | exact resolve eq372 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq506 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq92 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq507 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq506 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq3153 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq386 eq62
    | exact resolve eq62 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3163 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3153 eq386
    | exact resolve eq386 eq3153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386 eq3153
  have eq3178 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq3163 eq14
    | exact resolve eq14 eq3163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3163
  have eq3180 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq3178 X0
       have i₂ := eq385 (M.op sF4 sF4) (M.op (M.op sF4 sF4) X0)
       grind)
    | (have i₁ := eq3178 x
       have i₂ := eq385 (M.op sF4 sF4) x
       grind)
    | exact superpose eq385 eq3178
    | exact resolve eq3178 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3178
  have eq3222 : (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq387 eq62
    | exact resolve eq62 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3232 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq3222 eq387
    | exact resolve eq387 eq3222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq3416 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 X0 X0 x X0
       have i₂ := eq388 X0 X0 x
       grind)
    | exact superpose eq388 eq62
    | exact resolve eq62 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq3447 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq388 X0 X0 X0
       have i₂ := eq3416 X0
       grind)
    | exact superpose eq3416 eq388
    | exact resolve eq388 eq3416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3474 : ∀ X0 : G, (σ (σ (k X0 X0))) ≠ (σ (σ X0)) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq507 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq507
    | (have j0 := eq507 (σ X0)
       grind)
    | exact resolve eq507 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq3858 : ∀ X0 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X2)) X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq363 X0 X0 x X0 X2
       have i₂ := eq388 X0 X0 x
       grind)
    | exact superpose eq388 eq363
    | exact resolve eq363 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq4188 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ (k X0 x))) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq155 eq385
    | (have j1 := eq155 X0
       grind)
    | exact resolve eq385 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq4226 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) ≠ (M.op (M.op x y) (M.op x y)) ∨ (k X0 (M.op (M.op x y) (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq3232 eq13
    | (have j0 := eq13 X0 (M.op (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op x y) (M.op x y))
       have r₂ := eq3232
       grind)
    | exact resolve eq13 eq3232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3232
  have eq4236 : ∀ X0 : G, (k X0 (M.op (M.op x y) (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq4226 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4226
  have eq4268 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq4236 eq329
    | exact resolve eq329 eq4236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329 eq4236
  have eq4273 : ∀ X0 : G, (k X0 (τ (M.op (M.op x y) (M.op x y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq4268 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq4268
    | exact resolve eq4268 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4268
  have eq5695 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq364 X0 X0 x X0 X2 X3
       have i₂ := eq388 X0 X0 x
       grind)
    | exact superpose eq388 eq364
    | exact resolve eq364 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23126 : (σ x) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq3180 eq381
    | exact resolve eq381 eq3180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq23127 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq3180 eq14
    | exact resolve eq14 eq3180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3180
  have eq23168 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23127 X0
       have i₂ := eq3447 sF4
       grind)
    | exact superpose eq3447 eq23127
    | exact resolve eq23127 eq3447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23127
  have eq23169 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq23126
       have i₂ := eq3858 sF4 sF4
       grind)
    | exact superpose eq3858 eq23126
    | exact resolve eq23126 eq3858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3858 eq23126
  have eq23536 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq23169 eq61
    | exact resolve eq61 eq23169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq23169
  have eq23618 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) X1) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) := by
    intro X0 X1
    first
    | exact superpose eq23168 eq388
    | exact resolve eq388 eq23168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23643 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq23168 eq23618
    | exact resolve eq23618 eq23168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23168 eq23618
  have eq24621 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 X0
       have i₂ := eq23643 X0 X1
       grind)
    | exact superpose eq23643 eq14
    | exact resolve eq14 eq23643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25957 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq116 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25958 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq25957
    | exact resolve eq25957 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25957
  have eq25969 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq25958
       have r₂ := eq28
       grind)
    | exact resolve eq25958 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25958
  have eq25981 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq25969 eq73
    | exact resolve eq73 eq25969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq25969
  have eq26021 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq25981
       have r₂ := eq13 x (σ x)
       grind)
    | (have r₁ := eq25981
       have r₂ := eq13 x x
       grind)
    | exact resolve eq25981 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25981
  have eq26029 : (τ (σ y)) = (k y x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26021 eq78
    | exact resolve eq78 eq26021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq26030 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26021 eq116
    | exact resolve eq116 eq26021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq26021
  have eq26041 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq26030
  have eq26049 : y = (k y x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq26029
    | exact resolve eq26029 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26029
  have eq26053 : y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq26049
       have r₂ := eq13 x x
       grind)
    | exact resolve eq26049 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26049
  have eq26161 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq385 x x
       have i₂ := eq26041
       grind)
    | exact superpose eq26041 eq385
    | exact resolve eq385 eq26041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26041
  have eq26166 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26161
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq26161
    | exact resolve eq26161 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26161
  have eq26265 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq24621 x X0
       have i₂ := eq26166
       grind)
    | exact superpose eq26166 eq24621
    | exact resolve eq24621 eq26166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26166
  have eq27026 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq26265 y
       grind)
    | exact superpose eq26265 eq19
    | (have j1 := eq26265 y
       grind)
    | exact resolve eq19 eq26265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq26265
  have eq27084 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq27026
  have eq27483 : y = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27084 eq30
    | exact resolve eq30 eq27084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq27084
  have eq27626 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq27483
    | exact resolve eq27483 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq27483
  have eq27627 : y = (M.op x y) := by grind
  clear eq27626
  have eq27634 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq27627 eq21
    | exact resolve eq21 eq27627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq27803 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq27634
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq27634
    | exact resolve eq27634 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27634
  have eq27810 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq27803 eq27
    | exact resolve eq27 eq27803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30087 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X3)) X0) = X0 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq5695 X0 X2 X3
       have i₂ := eq24621 X0 (M.op X0 X2)
       grind)
    | exact superpose eq24621 eq5695
    | exact resolve eq5695 eq24621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5695
  have eq30223 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq3222 eq30087
    | exact resolve eq30087 eq3222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3222 eq30087
  have eq30342 : ∀ X0 : G, (M.op y y) = (M.op (M.op (M.op (M.op y y) X0) y) (M.op y y)) := by
    intro X0
    first
    | exact superpose eq27627 eq30223
    | exact resolve eq30223 eq27627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30223
  have eq30407 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 y) (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq30342 X0
       have i₂ := eq24621 y X0
       grind)
    | exact superpose eq24621 eq30342
    | exact resolve eq30342 eq24621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30342
  have eq30533 : ∀ X0 X1 : G, (M.op y y) = (M.op (M.op (M.op X0 y) (M.op (M.op y y) X1)) (M.op y y)) := by
    intro X0 X1
    first
    | (have i₁ := eq388 (M.op X0 y) (M.op y y) x
       have i₂ := eq30407 X0
       grind)
    | exact superpose eq30407 eq388
    | exact resolve eq388 eq30407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq30541 : ∀ X0 X1 : G, (M.op y y) = (M.op (M.op (M.op X0 y) X1) (M.op y y)) := by
    intro X0 X1
    first
    | (have i₁ := eq30533 X0 X1
       have i₂ := eq24621 y X1
       grind)
    | exact superpose eq24621 eq30533
    | exact resolve eq30533 eq24621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30533
  have eq36343 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 y) (M.op y y)) (M.op X1 X2)) (M.op X1 X3)) (M.op X1 X4)) X1) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq364 X1 (M.op X0 y) (M.op y y) X2 X3 X4
       have i₂ := eq30541 X0 X1
       grind)
    | exact superpose eq30541 eq364
    | exact resolve eq364 eq30541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364 eq30541
  have eq36394 : ∀ X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op y y) (M.op X1 X2)) (M.op X1 X3)) (M.op X1 X4)) X1) = X1 := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq36343 x X1 X2 X3 X4
       have i₂ := eq30407 x
       grind)
    | exact superpose eq30407 eq36343
    | exact resolve eq36343 eq30407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30407 eq36343
  have eq36417 : ∀ X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X3)) (M.op X1 X4)) X1) = X1 := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq36394 X1 X2 X3 X4
       have i₂ := eq24621 y (M.op X1 X2)
       grind)
    | exact superpose eq24621 eq36394
    | exact resolve eq36394 eq24621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36394
  have eq131070 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X0) (M.op (M.op X0 X0) X2)) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36417 (M.op X0 X0) X1 X0 X2
       have i₂ := eq3416 X0
       grind)
    | exact superpose eq3416 eq36417
    | exact resolve eq36417 eq3416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3416 eq36417
  have eq131963 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq131070 X0 X1 X2
       have i₂ := eq24621 X0 X2
       grind)
    | exact superpose eq24621 eq131070
    | exact resolve eq131070 eq24621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131070
  have eq132084 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X0) X2) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq131963 X0 X1 X2
       have i₂ := eq24621 X0 X1
       grind)
    | exact superpose eq24621 eq131963
    | exact resolve eq131963 eq24621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24621 eq131963
  have eq143206 : (σ (σ (τ (M.op (M.op x y) (M.op x y))))) ≠ (σ (σ (τ (M.op (M.op x y) (M.op x y))))) ∨ (σ (σ (τ (M.op (M.op x y) (M.op x y))))) = (M.op (σ (σ (τ (M.op (M.op x y) (M.op x y))))) (σ (σ (τ (M.op (M.op x y) (M.op x y)))))) := by
    first
    | exact superpose eq4273 eq3474
    | (have j0 := eq3474 (τ (M.op (M.op x y) (M.op x y)))
       grind)
    | exact resolve eq3474 eq4273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3474 eq4273
  have eq143310 : (σ (σ (τ (M.op (M.op x y) (M.op x y))))) = (M.op (σ (σ (τ (M.op (M.op x y) (M.op x y))))) (σ (σ (τ (M.op (M.op x y) (M.op x y)))))) := by grind
  clear eq143206
  have eq143390 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq143310
       have i₂ := eq15 (M.op sF0 sF0)
       grind)
    | exact superpose eq15 eq143310
    | exact resolve eq143310 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143310
  have eq143439 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
    first
    | exact superpose eq27627 eq143390
    | exact resolve eq143390 eq27627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27627 eq143390
  have eq151661 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq132084 X1 X0 X0
       have i₂ := eq23643 X0 X1
       grind)
    | exact superpose eq23643 eq132084
    | exact resolve eq132084 eq23643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23643 eq132084
  have eq155277 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4188 y
       have i₂ := eq26053
       grind)
    | exact superpose eq26053 eq4188
    | (have j0 := eq4188 y
       grind)
    | exact resolve eq4188 eq26053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4188 eq26053
  have eq155466 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq155277
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq155277
    | exact resolve eq155277 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155277
  have eq155488 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq155466
    | exact resolve eq155466 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155466
  have eq155499 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27803 eq155488
    | exact resolve eq155488 eq27803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155488
  have eq155503 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq155499
       have r₂ := eq28
       grind)
    | exact resolve eq155499 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155499
  have eq155506 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq155503
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq155503
    | exact resolve eq155503 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155503
  have eq155507 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27803 eq155506
    | exact resolve eq155506 eq27803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155506
  have eq166931 : ∀ X0 : G, (σ (M.op y y)) = (M.op X0 (σ (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq151661 X0 (σ (M.op y y))
       have i₂ := eq143439
       grind)
    | exact superpose eq143439 eq151661
    | exact resolve eq151661 eq143439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143439 eq151661
  have eq231654 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq155507 eq23536
    | exact resolve eq23536 eq155507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23536 eq155507
  have eq231878 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq231654
    | exact resolve eq231654 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq231654
  have eq231882 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27803 eq231878
    | exact resolve eq231878 eq27803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231878
  have eq231884 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq231882
       have r₂ := eq28
       grind)
    | exact resolve eq231882 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231882
  have eq232291 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq231884 eq385
    | exact resolve eq385 eq231884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385 eq231884
  have eq232326 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27810 eq232291
    | exact resolve eq232291 eq27810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232291
  have eq232344 : y = (M.op x x) := by
    first
    | (have r₁ := eq232326
       have r₂ := eq28
       grind)
    | exact resolve eq232326 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232326
  have eq232442 : y = (M.op y y) := by
    first
    | (have i₁ := eq3447 x
       have i₂ := eq232344
       grind)
    | exact superpose eq232344 eq3447
    | exact resolve eq3447 eq232344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3447 eq232344
  have eq232660 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq166931 X0
       have i₂ := eq232442
       grind)
    | exact superpose eq232442 eq166931
    | exact resolve eq166931 eq232442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166931 eq232442
  have eq232869 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq232660 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq232660
    | (have j0 := eq232660 X0
       grind)
    | exact resolve eq232660 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq232660
  have eq232897 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq27803 eq232869
    | exact resolve eq232869 eq27803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27803 eq232869
  have eq237448 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq232897 eq27810
    | exact resolve eq27810 eq232897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27810 eq232897
  have eq237697 : False := by grind
  exact eq237697

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxx_pxy_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq51 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
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
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq75 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq73 (σ X0)
       grind)
    | exact superpose eq73 eq10
    | exact resolve eq10 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq73 x
       grind)
    | exact superpose eq73 eq44
    | exact resolve eq44 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq77 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq73 sF2
       grind)
    | exact superpose eq73 eq50
    | exact resolve eq50 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq78 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq77
       have i₂ := eq73 x
       grind)
    | exact superpose eq73 eq77
    | exact resolve eq77 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq79 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq73 sF2
       grind)
    | exact superpose eq73 eq76
    | exact resolve eq76 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq80 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq75
    | exact resolve eq75 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq75
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq95
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq95
    | exact resolve eq95 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq431 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X0) X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq14
    | exact resolve eq14 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq494 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq53 x X0 X1 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 x X0 X1 y
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq506 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq506
    | exact resolve eq506 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq511 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq494 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq494
    | exact resolve eq494 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq518 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq508 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq508
    | (have j0 := eq508 x y
       grind)
    | exact resolve eq508 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3902 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 X0 x X0
       have i₂ := eq511 X0 X0 x
       grind)
    | exact superpose eq511 eq53
    | exact resolve eq53 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq511
  have eq3935 : x = (M.op (M.op (M.op x x) (M.op x y)) x) := by
    first
    | (have i₁ := eq502 x x
       have i₂ := eq3902 x
       grind)
    | exact superpose eq3902 eq502
    | exact resolve eq502 eq3902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502 eq3902
  have eq21913 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq21914 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq21913
    | exact resolve eq21913 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21913
  have eq21919 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq21914
       have r₂ := eq28
       grind)
    | exact resolve eq21914 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21914
  have eq21922 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq21919 eq78
    | exact resolve eq78 eq21919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21919
  have eq22002 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq21922
    | exact resolve eq21922 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21922
  have eq22003 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq22002
  have eq22014 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq79
       have i₂ := eq22003
       grind)
    | exact superpose eq22003 eq79
    | exact resolve eq79 eq22003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq22021 : x = (M.op (M.op x (M.op x y)) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3935
       have i₂ := eq22003
       grind)
    | exact superpose eq22003 eq3935
    | exact resolve eq3935 eq22003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3935
  have eq22024 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq431 x X0
       have i₂ := eq22003
       grind)
    | exact superpose eq22003 eq431
    | exact resolve eq431 eq22003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq22100 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq22024 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22024
    | (have j0 := eq22024 X0
       grind)
    | exact resolve eq22024 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22024
  have eq22102 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq518 eq22021
    | exact resolve eq22021 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq22021
  have eq22109 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq22014
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22014
    | exact resolve eq22014 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22014
  have eq22118 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq22100 X0
       have i₂ := eq508 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq22100 x
       have i₂ := eq508 sF2 x
       grind)
    | exact superpose eq508 eq22100
    | exact resolve eq22100 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508 eq22100
  have eq22277 : y = (M.op (M.op x x) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22102 eq51
    | exact resolve eq51 eq22102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq22102
  have eq23752 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22118 eq14
    | exact resolve eq14 eq22118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22118
  have eq24227 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq22277
       have i₂ := eq22003
       grind)
    | exact superpose eq22003 eq22277
    | exact resolve eq22277 eq22003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22003 eq22277
  have eq24252 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq24227
  have eq24261 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24252
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24252
    | exact resolve eq24252 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24252
  have eq24263 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq24261 eq30
    | exact resolve eq30 eq24261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24261
  have eq24304 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq24263
    | exact resolve eq24263 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24263
  have eq24305 : y = (M.op x y) ∨ x = y := by grind
  clear eq24304
  have eq24311 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq24305 eq21
    | exact resolve eq21 eq24305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24305
  have eq24440 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24311
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq24311
    | exact resolve eq24311 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24311
  have eq24470 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq24440 eq27
    | exact resolve eq27 eq24440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24440
  have eq44942 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22109 eq23752
    | exact resolve eq23752 eq22109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22109 eq23752
  have eq45039 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq44942 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44942
  have eq45441 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq45039 eq24470
    | exact resolve eq24470 eq45039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24470 eq45039
  have eq45524 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq45441
  have eq45545 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq45524
       have r₂ := eq28
       grind)
    | exact resolve eq45524 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45524
  have eq45552 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq45545 eq30
    | exact resolve eq30 eq45545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq45545
  have eq45718 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq45552
    | exact resolve eq45552 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq45552
  have eq45719 : x = y := by grind
  clear eq45718
  have eq45726 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq45719
       grind)
    | exact superpose eq45719 eq19
    | exact resolve eq19 eq45719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq45727 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq45719
       grind)
    | exact superpose eq45719 eq25
    | exact resolve eq25 eq45719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq45719
  have eq45851 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq45727
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq45727
    | exact resolve eq45727 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq45727
  have eq46300 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq45851 eq27
    | exact resolve eq27 eq45851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq45851
  have eq46529 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq46300 eq78
    | exact resolve eq78 eq46300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq46300
  have eq46596 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq46529
       have i₂ := eq45726
       grind)
    | exact superpose eq45726 eq46529
    | exact resolve eq46529 eq45726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45726 eq46529
  have eq46597 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46596 eq15
    | exact resolve eq15 eq46596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46596
  have eq46689 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq46597
    | exact resolve eq46597 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq46597
  have eq46712 : False := by grind
  exact eq46712

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_x_pxx_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq60 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq61 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
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
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq75 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq44
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq105
    | exact resolve eq105 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq323 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq343 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq62 X0 X1 X2 X3
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq62 x X0 X1 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq62
    | (have j0 := eq62 x X0 X1 y
       grind)
    | exact resolve eq62 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq62
    | (have j0 := eq62 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq62 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq62 X0 X1 X2 X3
       grind)
    | exact superpose eq62 eq14
    | exact resolve eq14 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq352 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq352
    | exact resolve eq352 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq357 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq343 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq343
    | exact resolve eq343 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq373 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq354 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq354
    | (have j0 := eq354 x y
       grind)
    | exact resolve eq354 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq354
    | (have j0 := eq354 (σ x) (σ y)
       grind)
    | exact resolve eq354 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq73 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq3384 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 X0 X0 x X0
       have i₂ := eq357 X0 X0 x
       grind)
    | exact superpose eq357 eq62
    | exact resolve eq62 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq3413 : x = (M.op (M.op (M.op x x) (M.op x y)) x) := by
    first
    | (have i₁ := eq346 x x
       have i₂ := eq3384 x
       grind)
    | exact superpose eq3384 eq346
    | exact resolve eq346 eq3384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq3414 : (σ x) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq347 sF2 sF2
       have i₂ := eq3384 sF2
       grind)
    | exact superpose eq3384 eq347
    | exact resolve eq347 eq3384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq3415 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq357 X0 X0 X0
       have i₂ := eq3384 X0
       grind)
    | exact superpose eq3384 eq357
    | exact resolve eq357 eq3384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3384
  have eq3446 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq436 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq436
    | (have j0 := eq436 (τ X0)
       grind)
    | exact resolve eq436 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq3456 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3446 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3446
    | (have j0 := eq3446 X0
       grind)
    | exact resolve eq3446 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3446
  have eq3463 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3456 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3456
    | (have j0 := eq3456 X0
       grind)
    | exact resolve eq3456 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3456
  have eq4728 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq3415 X0
       grind)
    | exact superpose eq3415 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq3415 X0
       grind)
    | exact resolve eq13 eq3415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3415
  have eq4734 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4728 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4728
  have eq4767 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq323 X0 (M.op X1 X1)
       have i₂ := eq4734 X1 (σ X0)
       grind)
    | exact superpose eq4734 eq323
    | exact resolve eq323 eq4734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq4774 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4767 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq4767
    | exact resolve eq4767 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4767
  have eq15571 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq106 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq15572 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq15571
    | exact resolve eq15571 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15571
  have eq15583 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq15572
       have r₂ := eq28
       grind)
    | exact resolve eq15572 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15572
  have eq15593 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq15583 eq4774
    | exact resolve eq4774 eq15583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15583
  have eq15634 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq29 eq15593
    | exact resolve eq15593 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15593
  have eq15642 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq15634 X0
       have j1 := eq13 X0 x
       grind)
    | (have r₁ := eq15634 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq15634 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15634
  have eq15683 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq436 x
       have i₂ := eq15642 x
       grind)
    | exact superpose eq15642 eq436
    | (have j0 := eq436 x
       grind)
    | exact resolve eq436 eq15642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15686 : x ≠ x ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3463 x
       have i₂ := eq15642 x
       grind)
    | exact superpose eq15642 eq3463
    | (have j0 := eq3463 x
       grind)
    | (have r₁ := eq3463 x
       have r₂ := eq15642 x
       grind)
    | exact resolve eq3463 eq15642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15642
  have eq15704 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq15686
  have eq15707 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq15683
  have eq15725 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15707
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15707
    | exact resolve eq15707 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15707
  have eq15787 : x = (M.op (M.op x (M.op x y)) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3413
       have i₂ := eq15704
       grind)
    | exact superpose eq15704 eq3413
    | exact resolve eq3413 eq15704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3413
  have eq15839 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq373 eq15787
    | exact resolve eq15787 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373 eq15787
  have eq16267 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq15725 eq3414
    | exact resolve eq3414 eq15725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3414
  have eq16319 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq375 eq16267
    | exact resolve eq16267 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375 eq16267
  have eq16608 : y = (M.op (M.op x x) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq15839 eq60
    | exact resolve eq60 eq15839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq15839
  have eq16873 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16319 eq61
    | exact resolve eq61 eq16319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq16319
  have eq18281 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16608
       have i₂ := eq15704
       grind)
    | exact superpose eq15704 eq16608
    | exact resolve eq16608 eq15704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15704 eq16608
  have eq18306 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18281
  have eq18315 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18306
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18306
    | exact resolve eq18306 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18306
  have eq18318 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq18315 eq30
    | exact resolve eq30 eq18315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18315
  have eq18439 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq18318
    | exact resolve eq18318 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18318
  have eq18440 : y = (M.op x y) ∨ x = y := by grind
  clear eq18439
  have eq18441 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq18440 eq21
    | exact resolve eq21 eq18440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18440
  have eq18570 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq18441
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18441
    | exact resolve eq18441 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18441
  have eq68682 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq15725 eq16873
    | exact resolve eq16873 eq15725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15725 eq16873
  have eq68715 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq68682
  have eq68728 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq68715
    | exact resolve eq68715 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68715
  have eq68730 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq68728 eq28
    | exact resolve eq28 eq68728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68728
  have eq68764 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq68730
       have r₂ := eq18570
       grind)
    | exact resolve eq68730 eq18570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18570 eq68730
  have eq68767 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq68764 eq30
    | exact resolve eq30 eq68764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq68764
  have eq69039 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq68767
    | exact resolve eq68767 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68767
  have eq69040 : x = y := by grind
  clear eq69039
  have eq69411 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq69040
       grind)
    | exact superpose eq69040 eq19
    | exact resolve eq19 eq69040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq69412 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq69040
       grind)
    | exact superpose eq69040 eq25
    | exact resolve eq25 eq69040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq69040
  have eq69606 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq69412
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq69412
    | exact resolve eq69412 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69412
  have eq69609 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq69606 eq27
    | exact resolve eq27 eq69606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq69606
  have eq69814 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq69411
       grind)
    | exact superpose eq69411 eq75
    | exact resolve eq75 eq69411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq69826 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq69411
       grind)
    | exact superpose eq69411 eq13
    | (have j0 := eq13 X0 x
       grind)
    | exact resolve eq13 eq69411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69831 : ∀ X0 : G, (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq4734 x X0
       have i₂ := eq69411
       grind)
    | exact superpose eq69411 eq4734
    | exact resolve eq4734 eq69411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4734
  have eq69866 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq69814
    | exact resolve eq69814 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69814
  have eq69890 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq69609 eq4774
    | exact resolve eq4774 eq69609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4774
  have eq70188 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq69831 eq436
    | (have j0 := eq436 (M.op x y)
       grind)
    | exact resolve eq436 eq69831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436 eq69831
  have eq70271 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq70188
  have eq70334 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq70271
    | exact resolve eq70271 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70271
  have eq71489 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq70334 eq357
    | exact resolve eq357 eq70334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq71495 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq71489 X0
       have i₂ := eq354 sF1 (M.op sF1 X0)
       grind)
    | (have i₁ := eq71489 x
       have i₂ := eq354 sF1 x
       grind)
    | exact superpose eq354 eq71489
    | exact resolve eq71489 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq71489
  have eq79062 : ∀ X0 : G, (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq71495 eq14
    | exact resolve eq14 eq71495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79107 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq70334 eq79062
    | exact resolve eq79062 eq70334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70334 eq79062
  have eq79121 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq79107 eq71495
    | exact resolve eq71495 eq79107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71495 eq79107
  have eq83332 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq69866
  have eq83345 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq69609 eq83332
    | exact resolve eq83332 eq69609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83332
  have eq83359 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq83345
       have r₂ := eq28
       grind)
    | exact resolve eq83345 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83345
  have eq83368 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq69609 eq83359
    | exact resolve eq83359 eq69609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83359
  have eq83412 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq83368 eq69890
    | exact resolve eq69890 eq83368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69890 eq83368
  have eq83421 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq83412
    | exact resolve eq83412 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq83412
  have eq83435 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq83421 X0
       have j1 := eq69826 X0
       grind)
    | (have r₁ := eq83421 X0
       have r₂ := eq69826 X0
       grind)
    | exact resolve eq83421 eq69826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69826 eq83421
  have eq83594 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3463 x
       have i₂ := eq83435 x
       grind)
    | exact superpose eq83435 eq3463
    | (have j0 := eq3463 x
       grind)
    | (have r₁ := eq3463 x
       have r₂ := eq83435 x
       grind)
    | exact resolve eq3463 eq83435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3463 eq83435
  have eq83673 : x = (M.op x x) := by grind
  clear eq83594
  have eq83745 : x = (M.op x y) := by
    first
    | (have i₁ := eq83673
       have i₂ := eq69411
       grind)
    | exact superpose eq69411 eq83673
    | exact resolve eq83673 eq69411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69411 eq83673
  have eq84095 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq83745 eq21
    | exact resolve eq21 eq83745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq83745
  have eq84425 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq84095
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq84095
    | exact resolve eq84095 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq84095
  have eq84786 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq84425 eq69609
    | exact resolve eq69609 eq84425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69609 eq84425
  have eq84789 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq79121 eq84786
    | exact resolve eq84786 eq79121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79121 eq84786
  have eq84856 : False := by grind
  exact eq84856

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxy_pxx_pxy_Equation2536 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq42 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
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
  have eq43 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) X2) X1 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X1) (σ X1)) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq94
    | (have j0 := eq94 X0 X1
       grind)
    | exact resolve eq94 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq131 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq42 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq42 X0 X1 X2 X3
       grind)
    | exact superpose eq42 eq42
    | exact resolve eq42 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq131 X0 x x X3 X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq131
    | exact resolve eq131 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq237 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq97 x y
       grind)
    | exact superpose eq97 eq16
    | (have j1 := eq97 (M.op y y) y
       grind)
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq405 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq42 X0 X0 x X0
       have i₂ := eq139 X0 X0 x
       grind)
    | exact superpose eq139 eq42
    | exact resolve eq42 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq139 X0 X0 X0
       have i₂ := eq405 X0
       grind)
    | exact superpose eq405 eq139
    | exact resolve eq139 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq405
  have eq534 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op X0 X0) X1
       have i₂ := eq431 X0
       grind)
    | exact superpose eq431 eq9
    | exact resolve eq9 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq550 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq534 X0 X1
       have i₂ := eq43 X0 X0 X1
       grind)
    | exact superpose eq43 eq534
    | exact resolve eq534 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq534
  have eq863 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X1 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42 X1 (M.op X0 X0) (M.op X0 X0) X2
       have i₂ := eq550 X0 X1
       grind)
    | exact superpose eq550 eq42
    | exact resolve eq42 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq864 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq550 X0 X1
       grind)
    | exact superpose eq550 eq9
    | exact resolve eq9 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq878 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq864 X0 X1
       have i₂ := eq431 X0
       grind)
    | exact superpose eq431 eq864
    | exact resolve eq864 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq879 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq863 X0 X1 X2
       have i₂ := eq431 X0
       grind)
    | exact superpose eq431 eq863
    | exact resolve eq863 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431 eq863
  have eq882 : ∀ X1 X2 : G, (M.op (M.op X1 X2) X1) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq879 x X1 X2
       have i₂ := eq878 x (M.op X1 X2)
       grind)
    | exact superpose eq878 eq879
    | exact resolve eq879 eq878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq945 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq878 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq878
    | exact resolve eq878 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq947 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq550 X1 X0
       have i₂ := eq878 X1 X0
       grind)
    | exact superpose eq878 eq550
    | exact resolve eq550 eq878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550 eq878
  have eq1153 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq882 (σ (M.op X1 X1)) X0
       have i₂ := eq945 X1 X0
       grind)
    | exact superpose eq945 eq882
    | exact resolve eq882 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882 eq945
  have eq2013 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq237
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq237
    | (have j1 := eq14 (M.op y y) y
       grind)
    | (have r₁ := eq237
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq237
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq237 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq2014 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq2013
  have eq18496 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2014
       grind)
    | exact superpose eq2014 eq16
    | exact resolve eq16 eq2014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2014
  have eq18497 : (σ x) = (σ y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq18496
       have r₂ := eq22 x
       grind)
    | exact resolve eq18496 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18496
  have eq1299610 : y = (τ (σ x)) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq18497
       grind)
    | exact superpose eq18497 eq10
    | exact resolve eq10 eq18497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18497
  have eq1300021 : x = y ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1299610
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1299610
    | exact resolve eq1299610 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299610
  have eq1300027 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1300021
       grind)
    | exact superpose eq1300021 eq16
    | exact resolve eq16 eq1300021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300021
  have eq1300028 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1300027
       have r₂ := eq22 x
       grind)
    | exact resolve eq1300027 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1300027
  have eq1306918 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1300028
       grind)
    | exact superpose eq1300028 eq10
    | exact resolve eq10 eq1300028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300028
  have eq1307360 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1306918
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1306918
    | exact resolve eq1306918 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306918
  have eq1307361 : y = (M.op y y) := by grind
  clear eq1307360
  have eq1307425 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq947 X0 y
       have i₂ := eq1307361
       grind)
    | exact superpose eq1307361 eq947
    | exact resolve eq947 eq1307361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq1307429 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1153 X0 y
       have i₂ := eq1307361
       grind)
    | exact superpose eq1307361 eq1153
    | exact resolve eq1153 eq1307361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153 eq1307361
  have eq1346368 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1307429 (σ x)
       grind)
    | exact superpose eq1307429 eq16
    | exact resolve eq16 eq1307429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1307429
  have eq1346668 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1346368
       have i₂ := eq1307425 x
       grind)
    | exact superpose eq1307425 eq1346368
    | exact resolve eq1346368 eq1307425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1307425 eq1346368
  have eq1346669 : False := by grind
  exact eq1346669

/-- `Equation2588`: `x = (y ◇ ((z ◇ y) ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pyx_pxx_pyx_Equation2588 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2588 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2588.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X1)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
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
  have eq53 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X0)) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op x (M.op (M.op x x) x))
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X1 X0) X0)) (M.op X0 (M.op (M.op X1 X0) X0))) = (k (M.op X0 (M.op (M.op X1 X0) X0)) (M.op X0 (M.op (M.op X1 X0) X0))) := by
    intro X0 X1
    grind
  have eq66 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (k (M.op X0 (M.op (M.op X1 X0) X0)) (M.op X0 (M.op (M.op X1 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 X1
       have i₂ := eq14 (M.op X0 (M.op (M.op X1 X0) X0)) X0 X1
       grind)
    | exact superpose eq14 eq65
    | exact resolve eq65 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq82 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq82
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq90
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq90
    | exact resolve eq90 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq96
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq156 : (σ (k (k x x) x)) = (k (k (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq40 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq40
    | exact resolve eq40 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq229 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq53 X0 (M.op X0 X0)
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq735 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq66 (M.op X0 X0) X0
       have i₂ := eq53 X0 (M.op X0 X0)
       grind)
    | exact superpose eq53 eq66
    | exact resolve eq66 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq66
  have eq887 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq889 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq76 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq890 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq889 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq892 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq887 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq898 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq892 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq892
    | (have j0 := eq892 X0
       grind)
    | exact resolve eq892 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq3021 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq890 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq890
    | (have j0 := eq890 (τ X0)
       grind)
    | exact resolve eq890 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq3030 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3021 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3021
    | (have j0 := eq3021 X0
       grind)
    | exact resolve eq3021 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3021
  have eq3036 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3030 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3030
    | (have j0 := eq3030 X0
       grind)
    | exact resolve eq3030 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3030
  have eq7563 : (σ (k (k x x) x)) = (M.op (σ x) (σ (k x x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq898 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq898
    | (have j0 := eq898 x
       grind)
    | exact resolve eq898 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq7612 : (σ (k (k x x) x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq7563
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq7563
    | exact resolve eq7563 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq7563
  have eq7627 : (k (k (σ x) (σ x)) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq7612
       have i₂ := eq156
       grind)
    | exact superpose eq156 eq7612
    | exact resolve eq7612 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq7612
  have eq22048 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22049 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq22048
    | exact resolve eq22048 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22048
  have eq22060 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq22049
       have r₂ := eq28
       grind)
    | exact resolve eq22049 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22049
  have eq22064 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq22060
  have eq22108 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq22064
    | exact resolve eq22064 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22064
  have eq22256 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22108 eq97
    | exact resolve eq97 eq22108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq22108
  have eq22267 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq22256
  have eq22270 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq22267
       have r₂ := eq28
       grind)
    | exact resolve eq22267 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22267
  have eq22274 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
  have eq22397 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq22274 eq50
    | exact resolve eq50 eq22274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq22274
  have eq25581 : (τ (σ x)) = (k x x) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq22270 eq22397
    | exact resolve eq22397 eq22270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22270 eq22397
  have eq25633 : (τ (σ x)) = (k x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq25581
  have eq25642 : x = (k x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq25633
    | exact resolve eq25633 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25633
  have eq25644 : y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq3036 x
       grind)
    | (have r₁ := eq25642
       have r₂ := eq3036 x
       grind)
    | exact resolve eq25642 eq3036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3036 eq25642
  have eq26067 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq25644
       grind)
    | exact superpose eq25644 eq89
    | exact resolve eq89 eq25644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq26069 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by grind
  have eq26111 : x ≠ y ∨ x = (M.op x x) := by grind
  clear eq25644
  have eq26120 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq26069
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq26069
    | exact resolve eq26069 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26069
  have eq26121 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq26067
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq26067
    | exact resolve eq26067 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26067
  have eq27218 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq26120
       grind)
    | exact superpose eq26120 eq73
    | exact resolve eq73 eq26120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq26120
  have eq27244 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq27218
    | exact resolve eq27218 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27218
  have eq31074 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq26121
       have r₂ := eq26111
       grind)
    | exact resolve eq26121 eq26111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26111 eq26121
  have eq37311 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq31074 eq7627
    | exact resolve eq7627 eq31074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7627
  have eq37323 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq37311
    | exact resolve eq37311 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37311
  have eq40349 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq37323 eq27244
    | exact resolve eq27244 eq37323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37323
  have eq40357 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq40349
  have eq40370 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq40357
       have r₂ := eq28
       grind)
    | exact resolve eq40357 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40357
  have eq40379 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq40370
  have eq40452 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq40379 eq31074
    | exact resolve eq31074 eq40379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31074 eq40379
  have eq40481 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq40452
  have eq40575 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq40481
  have eq40647 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq40575
    | exact resolve eq40575 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40575
  have eq40979 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq40647 eq27244
    | exact resolve eq27244 eq40647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27244 eq40647
  have eq40986 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq40979
  have eq40998 : x = (M.op x x) := by
    first
    | (have r₁ := eq40986
       have r₂ := eq28
       grind)
    | exact resolve eq40986 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40986
  have eq41012 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq229 x x
       have i₂ := eq40998
       grind)
    | exact superpose eq40998 eq229
    | exact resolve eq229 eq40998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41021 : (M.op x x) = (k (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq735 x
       have i₂ := eq40998
       grind)
    | exact superpose eq40998 eq735
    | exact resolve eq735 eq40998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq41095 : x = (k x x) := by
    first
    | (have i₁ := eq41021
       have i₂ := eq40998
       grind)
    | exact superpose eq40998 eq41021
    | exact resolve eq41021 eq40998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41021
  have eq41104 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq41012 X0
       have i₂ := eq40998
       grind)
    | exact superpose eq40998 eq41012
    | exact resolve eq41012 eq40998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40998 eq41012
  have eq41224 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq890 x
       have i₂ := eq41095
       grind)
    | exact superpose eq41095 eq890
    | (have j0 := eq890 x
       grind)
    | exact resolve eq890 eq41095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890 eq41095
  have eq41243 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq41224
  have eq41249 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq41243
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq41243
    | exact resolve eq41243 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq41243
  have eq41266 : y = (M.op x y) := by
    first
    | (have i₁ := eq41104 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq41104
    | (have j0 := eq41104 y
       grind)
    | exact resolve eq41104 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq41104
  have eq41553 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq41266 eq21
    | exact resolve eq21 eq41266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq41266
  have eq41709 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq41553
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq41553
    | exact resolve eq41553 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq41553
  have eq42275 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq41249 eq229
    | exact resolve eq229 eq41249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq42367 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq41249 eq42275
    | exact resolve eq42275 eq41249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41249 eq42275
  have eq42538 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq42367 eq27
    | (have j1 := eq42367 (σ y)
       grind)
    | exact resolve eq27 eq42367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq42367
  have eq42722 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41709 eq42538
    | exact resolve eq42538 eq41709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41709 eq42538
  have eq42737 : False := by grind
  exact eq42737

/-- `Equation2646`: `x = ((x ◇ x) ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation2646 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2646 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2646.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq79 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq83 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq54 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq54
    | exact resolve eq54 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq83
    | (have j0 := eq83 X0
       grind)
    | exact resolve eq83 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq83
  have eq92 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq91 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | (have j0 := eq91 X0
       grind)
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq93 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq92 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq92 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq92 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq96 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq93 (σ X0)
       grind)
    | exact superpose eq93 eq15
    | exact resolve eq15 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq96 X0
       have i₂ := eq93 X0
       grind)
    | exact superpose eq93 eq96
    | exact resolve eq96 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq123 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq77 x y
       grind)
    | exact superpose eq77 eq16
    | (have j1 := eq77 x y
       grind)
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq138 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq134
       have i₂ := eq107 y
       grind)
    | exact superpose eq107 eq134
    | exact resolve eq134 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq751 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79
    | (have j0 := eq79 X0 X1
       grind)
    | exact resolve eq79 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq792 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq751 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq751
    | (have j0 := eq751 X0 X1
       grind)
    | exact resolve eq751 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq815 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq138
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq138
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq138
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq138
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq138 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq816 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq815
  have eq5023 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq816
       grind)
    | exact superpose eq816 eq16
    | exact resolve eq16 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq5024 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5023
       have r₂ := eq107 x
       grind)
    | exact resolve eq5023 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5023
  have eq5123 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq123 y X0
       have i₂ := eq5024
       grind)
    | exact superpose eq5024 eq123
    | (have j0 := eq123 y X0
       grind)
    | (have r₁ := eq123 y x
       have r₂ := eq5024
       grind)
    | exact resolve eq123 eq5024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5024
  have eq5148 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq5123 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5123
  have eq5153 : ∀ X0 : G, (σ x) = (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq5148 X0
       have j1 := eq123 y X0
       grind)
    | (have r₁ := eq5148 X0
       have r₂ := eq123 y x
       grind)
    | exact resolve eq5148 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq5148
  have eq5155 : ∀ X0 : G, y = (τ (σ x)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq5153 X0
       grind)
    | exact superpose eq5153 eq10
    | (have j1 := eq5153 X0
       grind)
    | exact resolve eq10 eq5153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5153
  have eq5218 : ∀ X0 : G, x = y ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5155 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5155
    | (have j0 := eq5155 X0
       grind)
    | exact resolve eq5155 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5155
  have eq5322 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq5218 X0
       grind)
    | exact superpose eq5218 eq16
    | (have j1 := eq5218 X0
       grind)
    | exact resolve eq16 eq5218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5218
  have eq5323 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq5322 X0
       grind)
    | (have r₁ := eq5322 X0
       have r₂ := eq107 x
       grind)
    | exact resolve eq5322 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq5322
  have eq5348 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq5323 (σ X0)
       grind)
    | exact superpose eq5323 eq15
    | exact resolve eq15 eq5323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5323
  have eq5691 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5348 x
       grind)
    | exact superpose eq5348 eq16
    | exact resolve eq16 eq5348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5348
  have eq5927 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq5691
       have i₂ := eq792 x y
       grind)
    | exact superpose eq792 eq5691
    | (have j1 := eq792 x y
       grind)
    | (have r₁ := eq5691
       have r₂ := eq792 x y
       grind)
    | (have r₁ := eq5691
       have r₂ := eq792 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5691
       have r₂ := eq792 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5691 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq5928 : x = y ∨ y = (M.op y y) := by grind
  clear eq5927
  have eq5934 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq5691
       have i₂ := eq5928
       grind)
    | exact superpose eq5928 eq5691
    | exact resolve eq5691 eq5928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5928
  have eq5935 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq5934
       have i₂ := eq93 x
       grind)
    | exact superpose eq93 eq5934
    | exact resolve eq5934 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq5934
  have eq5936 : y = (M.op y y) := by grind
  clear eq5935
  have eq6040 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq5936
       grind)
    | exact superpose eq5936 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq5936
       grind)
    | exact resolve eq12 eq5936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5936
  have eq6069 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq6040 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6040
  have eq6125 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq5691
       have i₂ := eq6069 x
       grind)
    | exact superpose eq6069 eq5691
    | exact resolve eq5691 eq6069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5691 eq6069
  have eq6128 : False := by grind
  exact eq6128

/-- `Equation2653`: `x = ((x ◇ x) ◇ (y ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pyx_x_pxy_Equation2653 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2653 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2653.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X1) = X0 := by
    intro X0 X1
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
  have eq51 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq14 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq79 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq80 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq37 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq84 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
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
  have eq92 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq84
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq94
    | exact resolve eq94 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq97 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq71
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq71 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq16
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq97
  have eq121 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq38
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq132 : (k (σ (M.op x y)) (σ y)) = (σ (M.op (M.op x y) y)) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq121
       have i₂ := eq11 sF0 y
       grind)
    | exact superpose eq11 eq121
    | (have j1 := eq11 (M.op x y) y
       grind)
    | exact resolve eq121 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq121 eq16
    | exact resolve eq16 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq139 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq122
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq122
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq122 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq122 eq16
    | exact resolve eq16 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq139
  have eq334 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 X0)
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq335 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2824 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq338 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq338
    | exact resolve eq338 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq2829 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2824 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq2824
    | exact resolve eq2824 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2824
  have eq2831 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2829 X0
       have i₂ := eq51 (M.op X0 X0)
       grind)
    | exact superpose eq51 eq2829
    | exact resolve eq2829 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2829
  have eq2832 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2831 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq2831
    | exact resolve eq2831 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2831
  have eq2833 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq2832 (M.op X0 X0)
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq2832
    | exact resolve eq2832 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2837 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq2833 X0
       have i₂ := eq2832 X0
       grind)
    | exact superpose eq2832 eq2833
    | exact resolve eq2833 eq2832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2833
  have eq2978 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq79 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq79
    | (have j0 := eq79 x
       grind)
    | exact resolve eq79 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq2982 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2978
  have eq2986 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2982
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq2982
    | exact resolve eq2982 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2982
  have eq3002 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq2986
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq2986 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2986
  have eq3007 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3002 eq50
    | exact resolve eq50 eq3002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq3144 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq80 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq80
    | (have j0 := eq80 y
       grind)
    | exact resolve eq80 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq3147 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3144
  have eq3150 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3147
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq3147
    | exact resolve eq3147 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3147
  have eq3173 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq3150
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq3150 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3150
  have eq3194 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq3173 eq102
    | exact resolve eq102 eq3173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq3361 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq123
    | (have j0 := eq123 (M.op x y)
       grind)
    | exact resolve eq123 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq3363 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq3361
  have eq3365 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq122 eq3363
    | exact resolve eq3363 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq3363
  have eq3395 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq3365
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3365 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3365
  have eq3432 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq3395 eq145
    | exact resolve eq145 eq3395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq3500 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq334 X0
       have i₂ := eq2832 X0
       grind)
    | exact superpose eq2832 eq334
    | exact resolve eq334 eq2832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq2832
  have eq3505 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq3500 X0
       grind)
    | exact superpose eq3500 eq14
    | exact resolve eq14 eq3500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3506 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq3500 X0
       grind)
    | exact superpose eq3500 eq14
    | exact resolve eq14 eq3500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8758 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3002 eq92
    | exact resolve eq92 eq3002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq8764 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3173 eq103
    | exact resolve eq103 eq3173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq10110 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3395 eq146
    | exact resolve eq146 eq3395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq3395
  have eq11984 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq335 X0
       have i₂ := eq3505 X0 X1
       grind)
    | exact superpose eq3505 eq335
    | exact resolve eq335 eq3505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335 eq3505
  have eq12100 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11984 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq3500 X0
       grind)
    | exact superpose eq3500 eq11984
    | exact resolve eq11984 eq3500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12115 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11984 (M.op X0 X0) x
       have i₂ := eq14 X0 x
       grind)
    | exact superpose eq14 eq11984
    | exact resolve eq11984 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11984
  have eq12540 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq8758
       grind)
    | exact superpose eq8758 eq16
    | exact resolve eq16 eq8758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8758
  have eq12598 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3007 eq12540
    | exact resolve eq12540 eq3007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12540
  have eq12603 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq12598
       have r₂ := eq13 x x
       grind)
    | exact resolve eq12598 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12598
  have eq12605 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq12603
       grind)
    | exact superpose eq12603 eq44
    | exact resolve eq44 eq12603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq12630 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq3002 eq12605
    | exact resolve eq12605 eq3002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3002 eq12605
  have eq13218 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq8764
       grind)
    | exact superpose eq8764 eq16
    | exact resolve eq16 eq8764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8764
  have eq13280 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3194 eq13218
    | exact resolve eq13218 eq3194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13218
  have eq13285 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq13280
       have r₂ := eq13 y y
       grind)
    | exact resolve eq13280 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13280
  have eq13287 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq13285
       grind)
    | exact superpose eq13285 eq71
    | exact resolve eq71 eq13285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq13312 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq3173 eq13287
    | exact resolve eq13287 eq3173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3173 eq13287
  have eq14076 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq10110 eq16
    | exact resolve eq16 eq10110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10110
  have eq14142 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3432 eq14076
    | exact resolve eq14076 eq3432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14076
  have eq14147 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq14142
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq14142 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14142
  have eq16764 : x = (M.op (M.op (M.op x y) (M.op (M.op y y) y)) x) := by
    first
    | (have i₁ := eq12100 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12100
    | (have j0 := eq12100 y x
       grind)
    | exact resolve eq12100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16766 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (σ y)) (σ y))) (σ x)) := by
    first
    | exact superpose eq27 eq12100
    | (have j0 := eq12100 (σ y) (σ x)
       grind)
    | exact resolve eq12100 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20260 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20261 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq20260
    | exact resolve eq20260 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20260
  have eq20272 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq20261
       have r₂ := eq28
       grind)
    | exact resolve eq20261 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20261
  have eq20276 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20272 eq3007
    | exact resolve eq3007 eq20272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3007 eq20272
  have eq20334 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq20276
       have i₂ := eq12603
       grind)
    | exact superpose eq12603 eq20276
    | exact resolve eq20276 eq12603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12603 eq20276
  have eq20343 : y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq20334
    | exact resolve eq20334 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20334
  have eq20344 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq20343
  have eq20350 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20344 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq20344
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq20344
       grind)
    | exact resolve eq13 eq20344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20344
  have eq20351 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq20350
  have eq20359 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20351 eq96
    | exact resolve eq96 eq20351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq20351
  have eq20368 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by grind
  clear eq20359
  have eq20744 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq12115 x
       have i₂ := eq20368
       grind)
    | exact superpose eq20368 eq12115
    | exact resolve eq12115 eq20368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20368
  have eq20752 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20744
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20744
    | exact resolve eq20744 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20744
  have eq20768 : y = (M.op (M.op x (M.op (M.op x x) x)) y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12100 x y
       have i₂ := eq20752
       grind)
    | exact superpose eq20752 eq12100
    | exact resolve eq12100 eq20752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20752
  have eq20771 : y = (M.op (M.op x x) y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20768
       have i₂ := eq2837 x
       grind)
    | exact superpose eq2837 eq20768
    | exact resolve eq20768 eq2837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20768
  have eq21386 : x = (M.op y (M.op (M.op y y) y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3506 y x
       have i₂ := eq20771
       grind)
    | exact superpose eq20771 eq3506
    | exact resolve eq3506 eq20771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20771
  have eq21394 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21386
       have i₂ := eq2837 y
       grind)
    | exact superpose eq2837 eq21386
    | exact resolve eq21386 eq2837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21386
  have eq21743 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13312
       have i₂ := eq21394
       grind)
    | exact superpose eq21394 eq13312
    | exact resolve eq13312 eq21394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13312
  have eq21751 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq21394
       grind)
    | exact superpose eq21394 eq51
    | exact resolve eq51 eq21394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21394
  have eq21798 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21751
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq21751
    | exact resolve eq21751 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21751
  have eq21806 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21743
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21743
    | exact resolve eq21743 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21743
  have eq22292 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12630
       have i₂ := eq21798
       grind)
    | exact superpose eq21798 eq12630
    | exact resolve eq12630 eq21798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21798
  have eq22340 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq22292
    | exact resolve eq22292 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22292
  have eq22396 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21806 eq51
    | exact resolve eq51 eq21806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq21806
  have eq22443 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq22396
    | exact resolve eq22396 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22396
  have eq22783 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22443 eq22340
    | exact resolve eq22340 eq22443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22340 eq22443
  have eq22819 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq22783
  have eq22826 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq22819
       have r₂ := eq28
       grind)
    | exact resolve eq22819 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22819
  have eq22839 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22826 eq29
    | exact resolve eq29 eq22826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq22826
  have eq22972 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq22839
    | exact resolve eq22839 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22839
  have eq23045 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22972 eq21
    | exact resolve eq21 eq22972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23120 : x = (M.op (M.op y (M.op (M.op y y) y)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22972 eq16764
    | exact resolve eq16764 eq22972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16764 eq22972
  have eq23125 : x = (M.op (M.op y y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23120
       have i₂ := eq2837 y
       grind)
    | exact superpose eq2837 eq23120
    | exact resolve eq23120 eq2837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23120
  have eq23197 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23045
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq23045
    | exact resolve eq23045 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23045
  have eq24160 : y = (M.op x (M.op (M.op x x) x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3506 x y
       have i₂ := eq23125
       grind)
    | exact superpose eq23125 eq3506
    | exact resolve eq3506 eq23125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23125
  have eq24167 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24160
       have i₂ := eq2837 x
       grind)
    | exact superpose eq2837 eq24160
    | exact resolve eq24160 eq2837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24160
  have eq24175 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12630
       have i₂ := eq24167
       grind)
    | exact superpose eq24167 eq12630
    | exact resolve eq12630 eq24167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24167
  have eq24228 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24175
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq24175
    | exact resolve eq24175 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24175
  have eq24287 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24228 eq12115
    | exact resolve eq12115 eq24228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24228
  have eq24294 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq24287
    | exact resolve eq24287 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24287
  have eq24319 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24294 eq28
    | exact resolve eq28 eq24294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24294
  have eq24331 : x = (M.op x y) := by
    first
    | (have r₁ := eq24319
       have r₂ := eq23197
       grind)
    | exact resolve eq24319 eq23197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23197 eq24319
  have eq24382 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq24331 eq21
    | exact resolve eq21 eq24331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24541 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq24382
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24382
    | exact resolve eq24382 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24382
  have eq24592 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq24541 eq27
    | exact resolve eq27 eq24541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq26272 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq24331 eq132
    | exact resolve eq132 eq24331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq26273 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq26272
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq26272
    | exact resolve eq26272 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26272
  have eq26274 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq21 eq26273
    | exact resolve eq26273 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq26273
  have eq26275 : y = (M.op x x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq24331 eq26274
    | exact resolve eq26274 eq24331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26274
  have eq26276 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq24331 eq26275
    | exact resolve eq26275 eq24331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26275
  have eq26281 : (τ (σ (M.op x y))) = (k (M.op x y) y) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26276 eq138
    | exact resolve eq138 eq26276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq26276
  have eq26297 : (τ (σ (M.op x y))) = (k x y) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq24331 eq26281
    | exact resolve eq26281 eq24331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26281
  have eq26308 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq31 eq26297
    | exact resolve eq26297 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26297
  have eq26318 : y = (M.op x x) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq24331 eq26308
    | exact resolve eq26308 eq24331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26308
  have eq48107 : x = (k x y) ∨ x = (M.op y x) ∨ x = (k x y) ∨ x = (M.op y x) := by grind
  clear eq26318
  have eq48148 : x = (k x y) ∨ x = (M.op y x) := by grind
  clear eq48107
  have eq48738 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq48148
       grind)
    | exact superpose eq48148 eq45
    | exact resolve eq45 eq48148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq48148
  have eq48765 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq24541 eq48738
    | exact resolve eq48738 eq24541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48738
  have eq48778 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq48765
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq48765
    | exact resolve eq48765 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48765
  have eq48787 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq24541 eq48778
    | exact resolve eq48778 eq24541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48778
  have eq48813 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq48787 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq11 eq48787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48787
  have eq48814 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq24592 eq48813
    | exact resolve eq48813 eq24592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48813
  have eq48825 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq48814
       have r₂ := eq28
       grind)
    | exact resolve eq48814 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48814
  have eq50112 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq48825 eq12115
    | exact resolve eq12115 eq48825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48825
  have eq50121 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq24592 eq50112
    | exact resolve eq50112 eq24592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50112
  have eq50161 : (σ y) = (M.op (M.op (σ (M.op x y)) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq50121 eq12100
    | exact resolve eq12100 eq50121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50121
  have eq50164 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq50161
       have i₂ := eq2837 sF1
       grind)
    | exact superpose eq2837 eq50161
    | exact resolve eq50161 eq2837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50161
  have eq51316 : (σ (M.op x y)) = (M.op (σ y) (M.op (M.op (σ y) (σ y)) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq50164 eq3506
    | exact resolve eq3506 eq50164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50164
  have eq51324 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq51316
       have i₂ := eq2837 sF3
       grind)
    | exact superpose eq2837 eq51316
    | exact resolve eq51316 eq2837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51316
  have eq51331 : (τ (σ (M.op x y))) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq51324 eq3194
    | exact resolve eq3194 eq51324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3194 eq51324
  have eq51431 : (τ (σ (M.op x y))) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq51331
       have i₂ := eq13285
       grind)
    | exact superpose eq13285 eq51331
    | exact resolve eq51331 eq13285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13285 eq51331
  have eq51443 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq31 eq51431
    | exact resolve eq51431 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq51431
  have eq51452 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq24331 eq51443
    | exact resolve eq51443 eq24331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51443
  have eq52256 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq12115 y
       have i₂ := eq51452
       grind)
    | exact superpose eq51452 eq12115
    | exact resolve eq12115 eq51452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51452
  have eq52262 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq52256
  have eq52356 : y = (M.op (M.op x (M.op (M.op x x) x)) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12100 x y
       have i₂ := eq52262
       grind)
    | exact superpose eq52262 eq12100
    | exact resolve eq12100 eq52262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12100 eq52262
  have eq52359 : y = (M.op (M.op x x) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52356
       have i₂ := eq2837 x
       grind)
    | exact superpose eq2837 eq52356
    | exact resolve eq52356 eq2837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52356
  have eq52495 : x = (M.op y (M.op (M.op y y) y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3506 y x
       have i₂ := eq52359
       grind)
    | exact superpose eq52359 eq3506
    | exact resolve eq3506 eq52359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52359
  have eq52502 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52495
       have i₂ := eq2837 y
       grind)
    | exact superpose eq2837 eq52495
    | exact resolve eq52495 eq2837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52495
  have eq52534 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3500 y
       have i₂ := eq52502
       grind)
    | exact superpose eq52502 eq3500
    | exact resolve eq3500 eq52502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3500 eq52502
  have eq52573 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52534
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq52534
    | exact resolve eq52534 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52534
  have eq52610 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24331 eq52573
    | exact resolve eq52573 eq24331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52573
  have eq52795 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12630
       have i₂ := eq52610
       grind)
    | exact superpose eq52610 eq12630
    | exact resolve eq12630 eq52610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12630 eq52610
  have eq52867 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24541 eq52795
    | exact resolve eq52795 eq24541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52795
  have eq52877 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52867
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq52867
    | exact resolve eq52867 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52867
  have eq53380 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq52877 eq12115
    | exact resolve eq12115 eq52877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52877
  have eq53392 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24592 eq53380
    | exact resolve eq53380 eq24592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24592 eq53380
  have eq53393 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq53392
  have eq53431 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq53393 eq28
    | exact resolve eq28 eq53393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq53433 : (σ x) = (M.op (M.op (σ y) (M.op (M.op (σ y) (σ y)) (σ y))) (σ x)) := by
    first
    | exact superpose eq53393 eq16766
    | exact resolve eq16766 eq53393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16766 eq53393
  have eq53448 : (σ (M.op x y)) = (M.op (M.op (σ y) (M.op (M.op (σ y) (σ y)) (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq24541 eq53433
    | exact resolve eq53433 eq24541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53433
  have eq53451 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq53448
       have i₂ := eq2837 sF3
       grind)
    | exact superpose eq2837 eq53448
    | exact resolve eq53448 eq2837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53448
  have eq53575 : (σ y) = (M.op (σ (M.op x y)) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) := by
    first
    | exact superpose eq53451 eq3506
    | exact resolve eq3506 eq53451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3506 eq53451
  have eq53582 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq53575
       have i₂ := eq2837 sF1
       grind)
    | exact superpose eq2837 eq53575
    | exact resolve eq53575 eq2837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2837 eq53575
  have eq53585 : (τ (σ y)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq53582 eq3432
    | exact resolve eq3432 eq53582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3432 eq53582
  have eq53662 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq14147 eq53585
    | exact resolve eq53585 eq14147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14147 eq53585
  have eq53672 : (τ (σ y)) = (M.op x x) := by
    first
    | exact superpose eq24331 eq53662
    | exact resolve eq53662 eq24331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53662
  have eq53681 : y = (M.op x x) := by
    first
    | exact superpose eq30 eq53672
    | exact resolve eq53672 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq53672
  have eq53802 : y = (M.op x y) := by
    first
    | (have i₁ := eq12115 x
       have i₂ := eq53681
       grind)
    | exact superpose eq53681 eq12115
    | exact resolve eq12115 eq53681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12115 eq53681
  have eq53811 : y = (M.op x y) := by
    first
    | (have i₁ := eq53802
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53802
    | exact resolve eq53802 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq53802
  have eq53831 : x = y := by
    first
    | exact superpose eq24331 eq53811
    | exact resolve eq53811 eq24331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24331 eq53811
  have eq53852 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq53831
       grind)
    | exact superpose eq53831 eq25
    | exact resolve eq25 eq53831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq53831
  have eq54112 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq53852
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq53852
    | exact resolve eq53852 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq53852
  have eq54202 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24541 eq54112
    | exact resolve eq54112 eq24541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24541 eq54112
  have eq54282 : False := by grind
  exact eq54282

/-- `Equation2653`: `x = ((x ◇ x) ◇ (y ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxx_y_pxy_Equation2653 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2653 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2653.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq22 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq51 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq14 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) = (k (k (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq63 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    grind
  have eq64 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (k (M.op X0 X0) X0)) (M.op X0 X0)) = X1 := by
    intro X0 X1
    grind
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (k (M.op X0 X0) X0) (M.op X1 X1)) X1) := by
    intro X0 X1
    grind
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq81 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq46
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq81
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq82
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq82
    | exact resolve eq82 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq90
    | exact resolve eq90 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq111 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    grind
  have eq119 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k (M.op X0 X0) (k (M.op X0 X0) X0)) ∨ (M.op X0 X0) = (k (k (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq129 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq39
    | (have j0 := eq39 (M.op x y)
       grind)
    | exact resolve eq39 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq163 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq129 eq16
    | exact resolve eq16 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq188 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq163
       have i₂ := eq11 sF1 sF1
       grind)
    | exact superpose eq11 eq163
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq163 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq190 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq188
  have eq206 : ∀ X0 : G, (M.op X0 X0) = (M.op (k (k (M.op X0 X0) X0) (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    by_contra hcon
    push Not at hcon
    have f206_11 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) X0) = X0 := by
      intro X0
      grind
    have f206_16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
      intro X0 X1
      grind
    have f206_17 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X1) = X0 := by
      intro X0 X1
      grind
    have f206_20 : (M.op X0 X0) ≠ (M.op (k (k (M.op X0 X0) X0) (M.op X0 X0)) (M.op X0 X0)) := by grind
    have f206_26 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
      intro X0
      first
      | (have i₁ := f206_17 (M.op (M.op X0 X0) (M.op X0 X0)) X0
         have i₂ := f206_17 (M.op X0 X0) (M.op X0 X0)
         grind)
      | exact superpose f206_17 f206_17
      | exact resolve f206_17 f206_17
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f206_117 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
      intro X0
      grind
    have f206_118 : ∀ X0 : G, (M.op X0 X0) = (M.op (k (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op X0 X0)) := by
      intro X0
      first
      | (have i₁ := f206_11 (M.op X0 X0)
         have i₂ := f206_26 X0
         grind)
      | exact superpose f206_26 f206_11
      | exact resolve f206_11 f206_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f206_146 : (M.op X0 X0) ≠ (M.op (k (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op X0 X0)) := by
      first
      | (have i₁ := f206_20
         have i₂ := f206_117 X0
         grind)
      | exact superpose f206_117 f206_20
      | exact resolve f206_20 f206_117
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f206_150 : False := by
      first
      | (have r₁ := f206_146
         have r₂ := f206_118 X0
         grind)
      | exact resolve f206_146 f206_118
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f206_150
  have eq336 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  clear eq52
  have eq395 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq336 X0
       grind)
    | exact superpose eq336 eq63
    | exact resolve eq63 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq459 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X0)) (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X1
       have i₂ := eq336 X0
       grind)
    | exact superpose eq336 eq64
    | exact resolve eq64 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq546 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 X1
       have i₂ := eq336 X0
       grind)
    | exact superpose eq336 eq65
    | exact resolve eq65 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq599 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (M.op (k (M.op X0 X0) X0) (M.op X0 X0))) (k (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    have f599_11 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X0)) (M.op X0 X0)) = X1 := by
      intro X0 X1
      grind
    have f599_16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
      intro X0 X1
      grind
    have f599_17 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X1) = X0 := by
      intro X0 X1
      grind
    have f599_20 : X1 ≠ (M.op (M.op (M.op X1 X1) (M.op (k (M.op X0 X0) X0) (M.op X0 X0))) (k (M.op X0 X0) X0)) := by grind
    have f599_30 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
      intro X0
      first
      | (have i₁ := f599_17 (M.op (M.op X0 X0) (M.op X0 X0)) X0
         have i₂ := f599_17 (M.op X0 X0) (M.op X0 X0)
         grind)
      | exact superpose f599_17 f599_17
      | exact resolve f599_17 f599_17
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f599_124 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
      intro X0
      grind
    have f599_126 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0))) (M.op (M.op X0 X0) X0)) = X1 := by
      intro X0 X1
      first
      | (have i₁ := f599_11 (M.op X0 X0) X1
         have i₂ := f599_30 X0
         grind)
      | exact superpose f599_30 f599_11
      | exact resolve f599_11 f599_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f599_184 : X1 ≠ (M.op (M.op (M.op X1 X1) (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0))) (M.op (M.op X0 X0) X0)) := by
      first
      | (have i₁ := f599_20
         have i₂ := f599_124 X0
         grind)
      | exact superpose f599_124 f599_20
      | exact resolve f599_20 f599_124
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f599_188 : False := by
      first
      | (have r₁ := f599_184
         have r₂ := f599_126 X0 X1
         grind)
      | exact resolve f599_184 f599_126
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f599_188
  have eq600 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0))) (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq599 X0 X1
       have i₂ := eq336 X0
       grind)
    | exact superpose eq336 eq599
    | exact resolve eq599 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq644 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (M.op (M.op (M.op (k (M.op X0 X0) X0) (M.op X0 X0)) (M.op X1 X1)) X1) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    have f644_11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X1 X1)) X1) := by
      intro X0 X1
      grind
    have f644_16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
      intro X0 X1
      grind
    have f644_17 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X1) = X0 := by
      intro X0 X1
      grind
    have f644_20 : (k (M.op X0 X0) X0) ≠ (M.op (M.op (M.op (k (M.op X0 X0) X0) (M.op X0 X0)) (M.op X1 X1)) X1) := by grind
    have f644_30 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
      intro X0
      first
      | (have i₁ := f644_17 (M.op (M.op X0 X0) (M.op X0 X0)) X0
         have i₂ := f644_17 (M.op X0 X0) (M.op X0 X0)
         grind)
      | exact superpose f644_17 f644_17
      | exact resolve f644_17 f644_17
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f644_133 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
      intro X0
      grind
    have f644_134 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op X1 X1)) X1) := by
      intro X0 X1
      first
      | (have i₁ := f644_11 (M.op X0 X0) X1
         have i₂ := f644_30 X0
         grind)
      | exact superpose f644_30 f644_11
      | exact resolve f644_11 f644_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f644_206 : (M.op (M.op X0 X0) X0) ≠ (M.op (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op X1 X1)) X1) := by
      first
      | (have i₁ := f644_20
         have i₂ := f644_133 X0
         grind)
      | exact superpose f644_133 f644_20
      | exact resolve f644_20 f644_133
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f644_210 : False := by
      first
      | (have r₁ := f644_206
         have r₂ := f644_134 X0 X1
         grind)
      | exact resolve f644_206 f644_134
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f644_210
  have eq646 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq546 (M.op (M.op X0 X0) X0) X0
       have i₂ := eq459 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq459 eq546
    | exact resolve eq546 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq647 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq546 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq546
    | exact resolve eq546 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq650 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq647 X0
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq647
    | exact resolve eq647 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq651 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq646 X0
       have i₂ := eq395 X0
       grind)
    | exact superpose eq395 eq646
    | exact resolve eq646 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq653 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq644 X0 X1
       have i₂ := eq336 X0
       grind)
    | exact superpose eq336 eq644
    | exact resolve eq644 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq654 : ∀ X0 : G, (k (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    grind
  clear eq650
  have eq655 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq654 X0
       have i₂ := eq336 (M.op X0 X0)
       grind)
    | exact superpose eq336 eq654
    | exact resolve eq654 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq656 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    grind
  clear eq655
  have eq657 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq656 X0
       have i₂ := eq336 X0
       grind)
    | exact superpose eq336 eq656
    | exact resolve eq656 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq658 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (k (M.op X0 X0) X0) (M.op X0 X0)) (k (M.op X0 X0) X0)) := by
    intro X0
    grind
  have eq659 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq658 X0
       have i₂ := eq336 X0
       grind)
    | exact superpose eq336 eq658
    | exact resolve eq658 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq660 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq659 X0
       have i₂ := eq657 X0
       grind)
    | exact superpose eq657 eq659
    | exact resolve eq659 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq683 : ∀ X0 : G, (k (M.op (M.op X0 X0) X0) (M.op X0 X0)) = (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq62 X0
       have i₂ := eq336 X0
       grind)
    | exact superpose eq336 eq62
    | exact resolve eq62 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq723 : ∀ X0 : G, (k (M.op (k (M.op X0 X0) X0) (M.op X0 X0)) (k (M.op X0 X0) X0)) = (M.op (M.op (k (M.op X0 X0) X0) (M.op X0 X0)) (M.op (k (M.op X0 X0) X0) (M.op X0 X0))) := by
    intro X0
    grind
  have eq738 : ∀ X0 : G, (k (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq723 X0
       have i₂ := eq336 X0
       grind)
    | exact superpose eq336 eq723
    | exact resolve eq723 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq739 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq738 X0
       have i₂ := eq657 X0
       grind)
    | exact superpose eq657 eq738
    | exact resolve eq738 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq978 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) X0)) ∨ (M.op X0 X0) = (k (k (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq119 X0
       have i₂ := eq336 X0
       grind)
    | exact superpose eq336 eq119
    | (have j0 := eq119 X0
       grind)
    | exact resolve eq119 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq979 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) X0)) ∨ (M.op X0 X0) = (k (M.op (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq978 X0
       have i₂ := eq336 X0
       grind)
    | exact superpose eq336 eq978
    | (have j0 := eq978 X0
       grind)
    | exact resolve eq978 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq1026 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) (M.op X0 X0)) = (k (k (M.op X0 X0) X0) (M.op (k (M.op X0 X0) X0) (M.op X0 X0))) ∨ (k (M.op X0 X0) X0) = (k (M.op (k (M.op X0 X0) X0) (M.op X0 X0)) (k (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq979
  have eq1034 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = (k (M.op (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0))) ∨ (k (M.op X0 X0) X0) = (k (M.op (k (M.op X0 X0) X0) (M.op X0 X0)) (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1026 X0
       have i₂ := eq336 X0
       grind)
    | exact superpose eq336 eq1026
    | (have j0 := eq1026 X0
       grind)
    | exact resolve eq1026 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026
  have eq1035 : ∀ X0 : G, (k (M.op (M.op X0 X0) X0) X0) = X0 ∨ (k (M.op X0 X0) X0) = (k (M.op (k (M.op X0 X0) X0) (M.op X0 X0)) (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1034 X0
       have i₂ := eq657 X0
       grind)
    | exact superpose eq657 eq1034
    | (have j0 := eq1034 X0
       grind)
    | exact resolve eq1034 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034
  have eq1036 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op (M.op X0 X0) X0)) ∨ (k (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1035 X0
       have i₂ := eq336 X0
       grind)
    | exact superpose eq336 eq1035
    | (have j0 := eq1035 X0
       grind)
    | exact resolve eq1035 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035
  have eq1037 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op (M.op X0 X0) X0)) ∨ (k (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1036 X0
       have i₂ := eq657 X0
       grind)
    | exact superpose eq657 eq1036
    | (have j0 := eq1036 X0
       grind)
    | exact resolve eq1036 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq1038 : ∀ X0 : G, (k (M.op (M.op X0 X0) X0) X0) = X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1037 X0
       have i₂ := eq739 X0
       grind)
    | exact superpose eq739 eq1037
    | (have j0 := eq1037 X0
       grind)
    | exact resolve eq1037 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037
  have eq1084 : ∀ X0 : G, (k (M.op (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq651 X0
       have i₂ := eq683 X0
       grind)
    | exact superpose eq683 eq651
    | exact resolve eq651 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651 eq683
  have eq3022 : ∀ X0 : G, (M.op X0 X0) = (M.op (k (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq206 X0
       have i₂ := eq336 X0
       grind)
    | exact superpose eq336 eq206
    | exact resolve eq206 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq3023 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3022 X0
       have i₂ := eq1084 X0
       grind)
    | exact superpose eq1084 eq3022
    | exact resolve eq3022 eq1084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084 eq3022
  have eq3026 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3023 (σ x)
       have i₂ := eq75 x x
       grind)
    | exact superpose eq75 eq3023
    | (have j1 := eq75 X0 X0
       grind)
    | exact resolve eq3023 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq3029 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq3026 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3026
  have eq3081 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (k (M.op X0 X0) X0) (M.op X0 X0)) (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = (M.op (k (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    grind
  clear eq1038
  have eq3110 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = (M.op (k (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3081 X0
       have i₂ := eq336 X0
       grind)
    | exact superpose eq336 eq3081
    | (have j0 := eq3081 X0
       grind)
    | exact resolve eq3081 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3081
  have eq3119 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = (M.op (k (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3110 X0
       have i₂ := eq657 X0
       grind)
    | exact superpose eq657 eq3110
    | (have j0 := eq3110 X0
       grind)
    | exact resolve eq3110 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3110
  have eq3124 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3119 X0
       have i₂ := eq336 X0
       grind)
    | exact superpose eq336 eq3119
    | (have j0 := eq3119 X0
       grind)
    | exact resolve eq3119 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3119
  have eq3126 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3124 X0
       have i₂ := eq657 X0
       grind)
    | exact superpose eq657 eq3124
    | (have j0 := eq3124 X0
       grind)
    | exact resolve eq3124 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3124
  have eq3709 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq600 X0 X1
       have i₂ := eq657 X0
       grind)
    | exact superpose eq657 eq600
    | exact resolve eq600 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq3968 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq653 X0 X1
       have i₂ := eq657 X0
       grind)
    | exact superpose eq657 eq653
    | exact resolve eq653 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653 eq657
  have eq4069 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq395 X0
       have i₂ := eq3968 X0 X1
       grind)
    | exact superpose eq3968 eq395
    | exact resolve eq395 eq3968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395 eq3968
  have eq4111 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4069 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq3709 X0 X0
       grind)
    | exact superpose eq3709 eq4069
    | exact resolve eq4069 eq3709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4069
  have eq13270 : x = (M.op (M.op (M.op x y) (M.op (M.op y y) y)) x) := by
    first
    | (have i₁ := eq4111 y x
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq4111
    | (have j0 := eq4111 y x
       grind)
    | exact resolve eq4111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13272 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (σ y)) (σ y))) (σ x)) := by
    first
    | exact superpose eq28 eq4111
    | (have j0 := eq4111 (σ y) (σ x)
       grind)
    | exact resolve eq4111 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4111
  have eq16045 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq91 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16046 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq16045
    | exact resolve eq16045 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16045
  have eq16057 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq16046
       have r₂ := eq29
       grind)
    | exact resolve eq16046 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16046
  have eq16086 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16057 eq3023
    | exact resolve eq3023 eq16057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16057
  have eq16105 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq16086
    | exact resolve eq16086 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16086
  have eq16117 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16105 eq336
    | exact resolve eq336 eq16105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16105
  have eq16179 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq16117
    | exact resolve eq16117 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16117
  have eq16700 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16179 eq91
    | exact resolve eq91 eq16179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq16179
  have eq16708 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16700
  have eq16710 : y = (M.op x x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16708
       have r₂ := eq29
       grind)
    | exact resolve eq16708 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16708
  have eq16739 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3023 x
       have i₂ := eq16710
       grind)
    | exact superpose eq16710 eq3023
    | exact resolve eq3023 eq16710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16710
  have eq16758 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16739
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq16739
    | exact resolve eq16739 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16739
  have eq16770 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq336 y
       have i₂ := eq16758
       grind)
    | exact superpose eq16758 eq336
    | exact resolve eq336 eq16758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16758
  have eq16832 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16770
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq16770
    | exact resolve eq16770 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16770
  have eq17387 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq46
       have i₂ := eq16832
       grind)
    | exact superpose eq16832 eq46
    | exact resolve eq46 eq16832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq16832
  have eq17405 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22 eq17387
    | exact resolve eq17387 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17387
  have eq17458 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17405 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq17405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17461 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq17458
    | exact resolve eq17458 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17458
  have eq17472 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq17461
       have r₂ := eq29
       grind)
    | exact resolve eq17461 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17461
  have eq58920 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17472 eq3023
    | exact resolve eq3023 eq17472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17472
  have eq58978 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq58920
    | exact resolve eq58920 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58920
  have eq58979 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq58978
  have eq58992 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq58979 eq336
    | exact resolve eq336 eq58979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58979
  have eq59101 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq58992
    | exact resolve eq58992 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58992
  have eq60809 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq59101 eq17405
    | exact resolve eq17405 eq59101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17405 eq59101
  have eq60815 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq60809
  have eq60824 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq60815
       have r₂ := eq29
       grind)
    | exact resolve eq60815 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60815
  have eq60827 : (σ x) = (M.op (M.op (σ y) (M.op (M.op (σ y) (σ y)) (σ y))) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq60824 eq13272
    | exact resolve eq13272 eq60824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13272
  have eq60828 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq60827
       have i₂ := eq660 sF3
       grind)
    | exact superpose eq660 eq60827
    | exact resolve eq60827 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60827
  have eq61292 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ x)) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq60828 eq3709
    | exact resolve eq3709 eq60828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60828
  have eq61296 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq61292
       have i₂ := eq660 sF2
       grind)
    | exact superpose eq660 eq61292
    | exact resolve eq61292 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61292
  have eq61300 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ y)) (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq61296 eq14
    | exact resolve eq14 eq61296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61301 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  have eq61304 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61296 eq336
    | exact resolve eq336 eq61296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61315 : (σ y) = (k (σ x) (M.op (σ y) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61296 eq739
    | exact resolve eq739 eq61296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61326 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61296 eq3126
    | exact resolve eq3126 eq61296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3126 eq61296
  have eq61443 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61304 eq61301
    | exact resolve eq61301 eq61304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61301 eq61304
  have eq61446 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq61443
  have eq64986 : (σ y) = (M.op (M.op (M.op (σ y) (σ x)) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61446 eq61300
    | exact resolve eq61300 eq61446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61300 eq61446
  have eq64997 : (σ y) = (M.op (M.op (M.op (σ y) (σ x)) (σ y)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq64986
  have eq98757 : (τ (σ y)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61326 eq56
    | exact resolve eq56 eq61326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61326
  have eq98798 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq98757
    | exact resolve eq98757 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98757
  have eq98901 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq98798 eq64997
    | exact resolve eq64997 eq98798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64997 eq98798
  have eq98948 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ y = (k x y) := by grind
  clear eq98901
  have eq98966 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq28 eq98948
    | exact resolve eq98948 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98948
  have eq100582 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq60824 eq98966
    | exact resolve eq98966 eq60824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60824 eq98966
  have eq100637 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (k x y) := by grind
  clear eq100582
  have eq101633 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq100637 eq61315
    | exact resolve eq61315 eq100637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61315 eq100637
  have eq101698 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (k x y) := by grind
  clear eq101633
  have eq102524 : (τ (σ y)) = (k x y) ∨ y = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq101698 eq56
    | exact resolve eq56 eq101698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq101698
  have eq102571 : y = (k x y) ∨ y = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq31 eq102524
    | exact resolve eq102524 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq102524
  have eq102572 : y = (k x y) ∨ y = (M.op x y) := by grind
  clear eq102571
  have eq102618 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq102572
       grind)
    | exact superpose eq102572 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq102572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102644 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq102618
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq102618
    | exact resolve eq102618 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102618
  have eq102645 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq102644
  have eq103770 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3023 x
       have i₂ := eq102645
       grind)
    | exact superpose eq102645 eq3023
    | exact resolve eq3023 eq102645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3023 eq102645
  have eq103899 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq103770
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq103770
    | exact resolve eq103770 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103770
  have eq103900 : x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq103899
  have eq103955 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq336 y
       have i₂ := eq103900
       grind)
    | exact superpose eq103900 eq336
    | exact resolve eq336 eq103900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336 eq103900
  have eq104142 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq103955
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq103955
    | exact resolve eq103955 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq103955
  have eq104851 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq102572
       have i₂ := eq104142
       grind)
    | exact superpose eq104142 eq102572
    | exact resolve eq102572 eq104142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102572 eq104142
  have eq104867 : y = (M.op x y) := by grind
  clear eq104851
  have eq104914 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq104867 eq22
    | exact resolve eq22 eq104867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq105051 : x = (M.op (M.op y (M.op (M.op y y) y)) x) := by
    first
    | exact superpose eq104867 eq13270
    | exact resolve eq13270 eq104867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13270
  have eq105055 : x = (M.op (M.op y y) x) := by
    first
    | (have i₁ := eq105051
       have i₂ := eq660 y
       grind)
    | exact superpose eq660 eq105051
    | exact resolve eq105051 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105051
  have eq105185 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq104914
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq104914
    | exact resolve eq104914 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104914
  have eq105305 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq105185 eq28
    | exact resolve eq28 eq105185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq105652 : y = (M.op x (M.op (M.op x x) x)) := by
    first
    | (have i₁ := eq3709 x y
       have i₂ := eq105055
       grind)
    | exact superpose eq105055 eq3709
    | exact resolve eq3709 eq105055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3709 eq105055
  have eq105656 : y = (M.op x x) := by
    first
    | (have i₁ := eq105652
       have i₂ := eq660 x
       grind)
    | exact superpose eq660 eq105652
    | exact resolve eq105652 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660 eq105652
  have eq105661 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq105656
       grind)
    | exact superpose eq105656 eq88
    | exact resolve eq88 eq105656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq105718 : y = (k x (M.op y x)) := by
    first
    | (have i₁ := eq739 x
       have i₂ := eq105656
       grind)
    | exact superpose eq105656 eq739
    | exact resolve eq739 eq105656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq105828 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq105661
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq105661
    | exact resolve eq105661 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105661
  have eq105844 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq105185 eq105828
    | exact resolve eq105828 eq105185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105828
  have eq111610 : (τ (σ (M.op x y))) = (k x x) ∨ x = y := by
    first
    | exact superpose eq105844 eq51
    | exact resolve eq51 eq105844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq111678 : (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq32 eq111610
    | exact resolve eq111610 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111610
  have eq111687 : y = (k x x) ∨ x = y := by
    first
    | exact superpose eq104867 eq111678
    | exact resolve eq111678 eq104867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111678
  have eq111731 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq3029 x
       have i₂ := eq111687
       grind)
    | exact superpose eq111687 eq3029
    | (have j0 := eq3029 x
       grind)
    | exact resolve eq3029 eq111687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3029 eq111687
  have eq111763 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq111731
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq111731
    | exact resolve eq111731 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111731
  have eq111793 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq105185 eq111763
    | exact resolve eq111763 eq105185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111763
  have eq111824 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq111793
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq111793
    | exact resolve eq111793 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111793
  have eq111841 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq105305 eq111824
    | exact resolve eq111824 eq105305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111824
  have eq111857 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq111841
       have r₂ := eq29
       grind)
    | exact resolve eq111841 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111841
  have eq111864 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq111857
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq111857
    | exact resolve eq111857 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111857
  have eq112169 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq111864 eq111
    | exact resolve eq111 eq111864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq111864
  have eq112271 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by grind
  clear eq112169
  have eq112328 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq112271 eq105844
    | exact resolve eq105844 eq112271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105844 eq112271
  have eq112366 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq112328
  have eq112960 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq112366 eq30
    | exact resolve eq30 eq112366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq112366
  have eq113321 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32 eq112960
    | exact resolve eq112960 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq112960
  have eq113392 : x = y ∨ x = y := by
    first
    | exact superpose eq104867 eq113321
    | exact resolve eq113321 eq104867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113321
  have eq113393 : x = y := by grind
  clear eq113392
  have eq113441 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq113393
       grind)
    | exact superpose eq113393 eq26
    | exact resolve eq26 eq113393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq113878 : x = (k x (M.op x x)) := by
    first
    | (have i₁ := eq105718
       have i₂ := eq113393
       grind)
    | exact superpose eq113393 eq105718
    | exact resolve eq105718 eq113393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105718
  have eq113894 : x = (k x y) := by
    first
    | (have i₁ := eq113878
       have i₂ := eq105656
       grind)
    | exact superpose eq105656 eq113878
    | exact resolve eq113878 eq105656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105656 eq113878
  have eq114321 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq105185 eq113441
    | exact resolve eq113441 eq105185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105185 eq113441
  have eq114327 : x = (k x x) := by
    first
    | (have i₁ := eq113894
       have i₂ := eq113393
       grind)
    | exact superpose eq113393 eq113894
    | exact resolve eq113894 eq113393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113894
  have eq114711 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq114321
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq114321
    | exact resolve eq114321 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114321
  have eq115593 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq114711 eq105305
    | exact resolve eq105305 eq114711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105305
  have eq116139 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq115593 eq190
    | exact resolve eq190 eq115593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq115593
  have eq116285 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq116139
       have r₂ := eq29
       grind)
    | exact resolve eq116139 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116139
  have eq116310 : (k y y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq104867 eq116285
    | exact resolve eq116285 eq104867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104867 eq116285
  have eq116323 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq116310
       have i₂ := eq113393
       grind)
    | exact superpose eq113393 eq116310
    | exact resolve eq116310 eq113393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113393 eq116310
  have eq116334 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq116323
       have i₂ := eq114327
       grind)
    | exact superpose eq114327 eq116323
    | exact resolve eq116323 eq114327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114327 eq116323
  have eq116350 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq116334 eq15
    | exact resolve eq15 eq116334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116334
  have eq116779 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq116350
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq116350
    | exact resolve eq116350 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq116350
  have eq116956 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq114711 eq116779
    | exact resolve eq116779 eq114711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114711 eq116779
  have eq117071 : False := by grind
  exact eq117071
