import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4504`: `x ◇ (y ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_x_pyy_pyx_Equation4504 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4504 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4504.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  clear eq43
  have eq63 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op X0 (M.op X1 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X2 X3 (M.op x X5) X5
       have i₂ := eq14 X0 X1 x X5
       grind)
    | (have i₁ := eq14 X0 X1 X0 (M.op X1 X1)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq92
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq92
    | exact resolve eq92 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq98
    | exact resolve eq98 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq213 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq64 X0 (M.op x x)
       have i₂ := eq64 (M.op x x) x
       grind)
    | exact superpose eq64 eq64
    | exact resolve eq64 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq64 x x
       have i₂ := eq14 x x X0 X1
       grind)
    | (have i₁ := eq64 (M.op x (M.op X1 X1)) X1
       have i₂ := eq14 X0 X1 x (M.op X1 X1)
       grind)
    | exact superpose eq14 eq64
    | exact resolve eq64 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq65 x x
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq65
    | exact resolve eq65 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq226 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (M.op x y) y) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq224 eq14
    | exact resolve eq14 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) (σ y)) := by
    first
    | (have i₁ := eq226 x x
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq226
    | exact resolve eq226 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq359 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq213 eq13
    | (have j0 := eq13 X0 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op x y) y)
       have r₂ := eq213 (M.op (M.op x y) y)
       grind)
    | exact resolve eq13 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have j0 := eq359 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq368 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq363 eq34
    | exact resolve eq34 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 : G, (k X0 (σ (M.op (M.op x y) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq368 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq368
    | exact resolve eq368 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq477 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op (M.op x y) y) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq63 x x X2 X3 X5
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq63
    | exact resolve eq63 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq478 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X5) := by
    intro X5
    first
    | (have i₁ := eq477 x x X5
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq477
    | exact resolve eq477 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq688 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq78 X0 X0
       grind)
    | exact superpose eq78 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq78 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq78 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq13 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq78 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq696 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq695 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq698 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq688 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq706 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq698 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq698 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq698 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq1273 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq706 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq706
    | (have j0 := eq706 (τ X0) X1
       grind)
    | exact resolve eq706 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq1290 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1273 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1273
    | (have j0 := eq1273 X0 X1
       grind)
    | exact resolve eq1273 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273
  have eq1300 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1290 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1290
    | (have j0 := eq1290 X0 X1
       grind)
    | exact resolve eq1290 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq3648 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq696 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq696
    | (have j0 := eq696 (τ X0)
       grind)
    | exact resolve eq696 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq3665 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3648 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3648
    | (have j0 := eq3648 X0
       grind)
    | exact resolve eq3648 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3648
  have eq3675 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3665 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3665
    | (have j0 := eq3665 X0
       grind)
    | exact resolve eq3665 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3665
  have eq10484 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq10485 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq10484
    | exact resolve eq10484 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10484
  have eq10496 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq10485
       have r₂ := eq27
       grind)
    | exact resolve eq10485 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10485
  have eq10498 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq10496
    | exact resolve eq10496 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10496
  have eq10503 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq10498 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq10498
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq10498
       grind)
    | exact resolve eq13 eq10498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10498
  have eq10509 : ∀ X0 : G, x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq10503 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10503
  have eq10630 : ∀ X0 X1 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq10509 X1
       grind)
    | exact superpose eq10509 eq13
    | (have j0 := eq13 X0 x
       have j1 := eq10509 X1
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq10509 X0
       grind)
    | exact resolve eq13 eq10509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10509
  have eq10635 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq10630 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10630
  have eq10663 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq49
       have i₂ := eq10635 (k sF2 sF2) x
       grind)
    | exact superpose eq10635 eq49
    | (have j1 := eq10635 X0 x
       grind)
    | exact resolve eq49 eq10635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10635
  have eq10745 : ∀ X0 : G, x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq10663
    | (have j0 := eq10663 x
       grind)
    | exact resolve eq10663 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10663
  have eq10771 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq10745 X0
       have j1 := eq1300 x X0
       grind)
    | (have r₁ := eq10745 X0
       have r₂ := eq1300 x x
       grind)
    | (have r₁ := eq10745 x
       have r₂ := eq1300 x x
       grind)
    | exact resolve eq10745 eq1300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300 eq10745
  have eq10812 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq696 x
       have i₂ := eq10771 x
       grind)
    | exact superpose eq10771 eq696
    | (have j0 := eq696 x
       grind)
    | exact resolve eq696 eq10771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696 eq10771
  have eq10834 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10812
  have eq10853 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10834
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10834
    | exact resolve eq10834 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10834
  have eq11232 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq10853 eq64
    | exact resolve eq64 eq10853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13188 : (σ x) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11232 eq10853
    | exact resolve eq10853 eq11232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10853 eq11232
  have eq13191 : (σ x) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13188
  have eq13212 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13191 eq227
    | exact resolve eq227 eq13191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq13191
  have eq13249 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13212
    | exact resolve eq13212 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13212
  have eq13250 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13249
  have eq13252 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13250 eq224
    | exact resolve eq224 eq13250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq13255 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq13252
    | exact resolve eq13252 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13252
  have eq13260 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13255 eq213
    | exact resolve eq213 eq13255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq13263 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13255 eq363
    | exact resolve eq363 eq13255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq13266 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13255 eq478
    | exact resolve eq478 eq13255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13255
  have eq13299 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13250 eq13260
    | exact resolve eq13260 eq13250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13260
  have eq13322 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq13299 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13299
  have eq13334 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13250 eq13263
    | exact resolve eq13263 eq13250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13263
  have eq13363 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq13334 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13334
  have eq13379 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13250 eq13266
    | exact resolve eq13266 eq13250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13250 eq13266
  have eq13410 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq13379 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13379
  have eq13419 : (σ x) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13322 (M.op x sF2)
       have i₂ := eq215 x sF2
       grind)
    | exact superpose eq215 eq13322
    | exact resolve eq13322 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13322
  have eq13488 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13363 eq49
    | exact resolve eq49 eq13363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq13363
  have eq13572 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq13488
    | exact resolve eq13488 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq13488
  have eq13752 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq13572
       grind)
    | exact superpose eq13572 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq13572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13572
  have eq13753 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq13752
  have eq13964 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq64 X0 x
       have i₂ := eq13753
       grind)
    | exact superpose eq13753 eq64
    | exact resolve eq64 eq13753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq21221 : ∀ X0 : G, (σ x) = (M.op X0 x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13964 eq13419
    | exact resolve eq13419 eq13964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13419 eq13964
  have eq21246 : ∀ X0 : G, (σ x) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21221 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21221
  have eq21536 : x = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13753
       have i₂ := eq21246 x
       grind)
    | exact superpose eq21246 eq13753
    | exact resolve eq13753 eq21246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13753 eq21246
  have eq21548 : x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq21536
  have eq21650 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21548 eq13410
    | exact resolve eq13410 eq21548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13410 eq21548
  have eq21691 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21650 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21650
  have eq23123 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq21691 y
       grind)
    | exact superpose eq21691 eq18
    | (have j1 := eq21691 y
       grind)
    | exact resolve eq18 eq21691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21691
  have eq23169 : x = (M.op x y) := by grind
  clear eq23123
  have eq23190 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq23169 eq20
    | exact resolve eq20 eq23169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23246 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq23169 eq369
    | exact resolve eq369 eq23169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq23248 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq23169 eq478
    | exact resolve eq478 eq23169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq23294 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq23248 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23248
    | (have j0 := eq23248 X0
       grind)
    | exact resolve eq23248 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23248
  have eq23296 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq23246 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23246
    | (have j0 := eq23246 X0
       grind)
    | exact resolve eq23246 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23246
  have eq23350 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq23190
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23190
    | exact resolve eq23190 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq23190
  have eq23362 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq23169 eq23294
    | exact resolve eq23294 eq23169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23294
  have eq23364 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq23296
    | (have j0 := eq23296 X0
       grind)
    | exact resolve eq23296 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq23296
  have eq23733 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq23350 eq26
    | exact resolve eq26 eq23350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq23350
  have eq24021 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq23364 eq3675
    | (have j0 := eq3675 (σ (M.op x y))
       grind)
    | (have r₁ := eq3675 (σ (M.op x y))
       have r₂ := eq23364 (σ (M.op x y))
       grind)
    | exact resolve eq3675 eq23364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3675 eq23364
  have eq24049 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq24021
  have eq25132 : (M.op (M.op x y) y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq24049 eq215
    | exact resolve eq215 eq24049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq25140 : (σ (M.op x y)) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq24049 eq25132
    | exact resolve eq25132 eq24049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24049 eq25132
  have eq25146 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq23169 eq25140
    | exact resolve eq25140 eq23169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25140
  have eq25152 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq25146
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25146
    | exact resolve eq25146 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq25146
  have eq25158 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq23169 eq25152
    | exact resolve eq25152 eq23169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23169 eq25152
  have eq25233 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq25158 eq23733
    | exact resolve eq23733 eq25158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23733
  have eq25236 : x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25233
       have i₂ := eq23362 sF3
       grind)
    | exact superpose eq23362 eq25233
    | exact resolve eq25233 eq23362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23362 eq25233
  have eq25453 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq25236 eq27
    | exact resolve eq27 eq25236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq25236
  have eq25487 : False := by grind
  exact eq25487

/-- `Equation4513`: `x ◇ (y ◇ z) = (x ◇ y) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_y_pxy_Equation4513 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4513 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4513.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq54 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X3 (M.op X0 X1)) X5) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X3 (M.op X0 X1) x X5
       have i₂ := eq14 X0 X1 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op x (M.op y X0)) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0 X1
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 X1 X2 x
       have i₂ := eq14 X0 X1 X3 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq16
    | exact resolve eq16 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ y = (k x y) := by
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
  have eq78 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq96
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq98
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq98
    | exact resolve eq98 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq105 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq109 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq105
  have eq110 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq109
  have eq141 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq16
    | exact resolve eq16 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq318 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq35
  have eq329 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq318 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq318
    | exact resolve eq318 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq330 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq329
  have eq461 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 x y X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61
    | (have j0 := eq61 X0 x X1 y
       grind)
    | exact resolve eq61 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq466 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq61
    | (have j0 := eq61 X0 (σ x) X1 (σ y)
       grind)
    | exact resolve eq61 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq598 : ∀ X0 X1 : G, (M.op (M.op X0 x) X1) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq461 X0 x
       have i₂ := eq14 X0 x x X1
       grind)
    | exact superpose eq14 eq461
    | (have j1 := eq14 X0 x y X1
       grind)
    | exact resolve eq461 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq466 X0 x
       have i₂ := eq14 X0 sF2 x x
       grind)
    | exact superpose eq14 eq466
    | (have j1 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq466 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1278 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ x) (M.op (σ y) X2))) = (M.op (M.op X0 (M.op (σ x) (σ y))) X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq27 eq54
    | (have j0 := eq54 (σ x) (σ y) X2 X0 X1
       grind)
    | exact resolve eq54 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1518 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq466 eq1278
    | exact resolve eq1278 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278
  have eq2749 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq74 eq330
    | exact resolve eq330 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq2777 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq466 eq2749
    | exact resolve eq2749 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2749
  have eq2779 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq639 eq2777
    | exact resolve eq2777 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639 eq2777
  have eq2781 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op (M.op x x) (M.op x y))) := by
    first
    | (have i₁ := eq2779
       have i₂ := eq461 (M.op x x) x
       grind)
    | exact superpose eq461 eq2779
    | exact resolve eq2779 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461 eq2779
  have eq2782 : (σ (M.op x (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2781
       have i₂ := eq598 x sF0
       grind)
    | exact superpose eq598 eq2781
    | exact resolve eq2781 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2781
  have eq2785 : (M.op x (M.op x y)) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2782 eq16
    | exact resolve eq16 eq2782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343888 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343938 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq343888
    | exact resolve eq343888 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343888
  have eq343954 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq343938
       have r₂ := eq28
       grind)
    | exact resolve eq343938 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343938
  have eq343957 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq343954
    | exact resolve eq343954 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343954
  have eq343966 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq343957 eq78
    | (have r₁ := eq78
       have r₂ := eq343957
       grind)
    | exact resolve eq78 eq343957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq343957
  have eq344149 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq343966
  have eq344150 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq344149
  have eq344345 : (τ (σ y)) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq344150 eq66
    | exact resolve eq66 eq344150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq344346 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq344150 eq99
    | exact resolve eq99 eq344150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq344150
  have eq344372 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq344346
  have eq344386 : y = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq30 eq344345
    | exact resolve eq344345 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344345
  have eq344397 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq344386
       have r₂ := eq77
       grind)
    | exact resolve eq344386 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq344386
  have eq344663 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq344397
       grind)
    | exact superpose eq344397 eq49
    | exact resolve eq49 eq344397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq344397
  have eq344708 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq344663
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq344663
    | exact resolve eq344663 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344663
  have eq344845 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq344708 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq344708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344708
  have eq344858 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq344845
  have eq344873 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq344858
    | exact resolve eq344858 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344858
  have eq344886 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq344873
    | exact resolve eq344873 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344873
  have eq344893 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52
       have i₂ := eq344372
       grind)
    | exact superpose eq344372 eq52
    | exact resolve eq52 eq344372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq344906 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op x y) X0) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq598 x X0
       have i₂ := eq344372
       grind)
    | exact superpose eq344372 eq598
    | exact resolve eq598 eq344372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598 eq344372
  have eq345210 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq344893
    | exact resolve eq344893 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344893
  have eq346806 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq344886 eq345210
    | exact resolve eq345210 eq344886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344886 eq345210
  have eq346978 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq346806
  have eq347103 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq346978
       have r₂ := eq28
       grind)
    | exact resolve eq346978 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346978
  have eq347207 : (M.op x (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq347103 eq2785
    | exact resolve eq2785 eq347103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2785
  have eq347291 : (M.op x (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq347207
    | exact resolve eq347207 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347207
  have eq351662 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq347291 eq2782
    | exact resolve eq2782 eq347291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351918 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq351662
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq351662
    | exact resolve eq351662 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351662
  have eq352007 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq351918 eq1518
    | exact resolve eq1518 eq351918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518 eq351918
  have eq352353 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq347103 eq352007
    | exact resolve eq352007 eq347103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347103 eq352007
  have eq352868 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq352353 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352353
  have eq352988 : (τ (σ y)) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq352868 eq141
    | exact resolve eq141 eq352868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq352868
  have eq353418 : y = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30 eq352988
    | exact resolve eq352988 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352988
  have eq353938 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq59 y X0
       have i₂ := eq353418
       grind)
    | exact superpose eq353418 eq59
    | exact resolve eq59 eq353418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq353418
  have eq354149 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq353938 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq353938
    | (have j0 := eq353938 X0
       grind)
    | exact resolve eq353938 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353938
  have eq359549 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3, g4, g5, g6⟩ := hcon
    have f359549_18 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x y)) := by
      intro X0
      grind
    have f359549_19 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x (M.op x y)) ∨ (σ y) = (σ (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
      intro X0
      grind
    have f359549_25 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X1) X3) := by
      intro X0 X1 X2 X3
      grind
    have f359549_28 : (M.op x y) ≠ (M.op x (M.op x y)) := by grind
    have f359549_32 : (σ y) ≠ (σ (M.op x y)) := by grind
    have f359549_33 : x ≠ y := by grind
    have f359549_34 : (σ x) ≠ (σ y) := by grind
    have f359549_36 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
      intro X0
      first
      | (have j0 := f359549_19 X0
         grind)
      | (have r₁ := f359549_19 X0
         have r₂ := f359549_32
         grind)
      | exact resolve f359549_19 f359549_32
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f359549_37 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x y)) := by
      intro X0
      first
      | (have j0 := f359549_18 X0
         grind)
      | (have r₁ := f359549_18 X0
         have r₂ := f359549_33
         grind)
      | exact resolve f359549_18 f359549_33
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f359549_38 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) := by
      intro X0
      first
      | (have j0 := f359549_36 X0
         grind)
      | (have r₁ := f359549_36 X0
         have r₂ := f359549_33
         grind)
      | exact resolve f359549_36 f359549_33
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f359549_39 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (σ y) = (σ (M.op x y)) := by
      intro X0
      first
      | (have j0 := f359549_37 X0
         grind)
      | (have r₁ := f359549_37 X0
         have r₂ := f359549_34
         grind)
      | exact resolve f359549_37 f359549_34
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f359549_40 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x (M.op x y)) := by
      intro X0
      first
      | (have j0 := f359549_38 X0
         grind)
      | (have r₁ := f359549_38 X0
         have r₂ := f359549_34
         grind)
      | exact resolve f359549_38 f359549_34
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f359549_41 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
      intro X0
      first
      | (have j0 := f359549_39 X0
         grind)
      | (have r₁ := f359549_39 X0
         have r₂ := f359549_32
         grind)
      | exact resolve f359549_39 f359549_32
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f359549_55 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op (M.op X0 (M.op x y)) X2) := by
      intro X0 X2
      first
      | (have i₁ := f359549_25 X0 (M.op x y) x X2
         have i₂ := f359549_41 x
         grind)
      | exact superpose f359549_41 f359549_25
      | exact resolve f359549_25 f359549_41
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f359549_67 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) X1) := by
      intro X0 X1
      first
      | (have i₁ := f359549_41 (M.op X0 x)
         have i₂ := f359549_25 (M.op x y) X0 x X1
         grind)
      | exact superpose f359549_25 f359549_41
      | exact resolve f359549_41 f359549_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f359549_69 : ∀ X1 : G, (M.op x y) = (M.op (M.op x (M.op x y)) X1) := by
      intro X1
      first
      | (have i₁ := f359549_67 x X1
         have i₂ := f359549_40 x
         grind)
      | exact superpose f359549_40 f359549_67
      | exact resolve f359549_67 f359549_40
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f359549_72 : (M.op x y) = (M.op x (M.op x y)) := by
      first
      | (have i₁ := f359549_69 x
         have i₂ := f359549_55 x x
         grind)
      | exact superpose f359549_55 f359549_69
      | exact resolve f359549_69 f359549_55
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f359549_74 : False := by
      first
      | (have r₁ := f359549_72
         have r₂ := f359549_28
         grind)
      | exact resolve f359549_72 f359549_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f359549_74
  clear eq344906 eq354149
  have eq359923 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq359549
  have eq360418 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq359923 eq347291
    | exact resolve eq347291 eq359923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347291 eq359923
  have eq360579 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq360418
  have eq360765 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq360579 eq15
    | exact resolve eq15 eq360579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360579
  have eq360810 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq360765
    | exact resolve eq360765 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360765
  have eq360814 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq360810
       have r₂ := eq28
       grind)
    | exact resolve eq360810 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360810
  have eq360819 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq360814 eq30
    | exact resolve eq30 eq360814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360814
  have eq360949 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq360819
    | exact resolve eq360819 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq360819
  have eq360950 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq360949
  have eq363101 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq360950 eq27
    | exact resolve eq27 eq360950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363102 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq360950 eq30
    | exact resolve eq30 eq360950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq360950
  have eq363366 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq363102
    | exact resolve eq363102 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq363102
  have eq363464 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq363366 eq2782
    | exact resolve eq2782 eq363366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2782 eq363366
  have eq363590 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq363464
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq363464
    | exact resolve eq363464 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363464
  have eq363642 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq21 eq363590
    | exact resolve eq363590 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363590
  have eq366105 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq363642 eq466
    | exact resolve eq466 eq363642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq383342 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq366105 eq363642
    | exact resolve eq363642 eq366105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363642 eq366105
  have eq383427 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by grind
  clear eq383342
  have eq383798 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq383427 eq363101
    | exact resolve eq363101 eq383427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363101 eq383427
  have eq383964 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq383798
  have eq384044 : x = y := by
    first
    | (have r₁ := eq383964
       have r₂ := eq28
       grind)
    | exact resolve eq383964 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383964
  have eq384096 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq384044
       grind)
    | exact superpose eq384044 eq19
    | exact resolve eq19 eq384044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq384097 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq384044
       grind)
    | exact superpose eq384044 eq25
    | exact resolve eq25 eq384044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq384044
  have eq384254 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq384097
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq384097
    | exact resolve eq384097 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq384097
  have eq384277 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq384254 eq27
    | exact resolve eq27 eq384254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq384254
  have eq384943 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq384277 eq74
    | exact resolve eq74 eq384277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq384277
  have eq385255 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq384943
       have i₂ := eq384096
       grind)
    | exact superpose eq384096 eq384943
    | exact resolve eq384943 eq384096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384096 eq384943
  have eq385357 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq385255 eq15
    | exact resolve eq15 eq385255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385255
  have eq385402 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq385357
    | exact resolve eq385357 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq385357
  have eq385410 : False := by grind
  exact eq385410

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_x_pyx_pyx_pxy_Equation452 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq175 : ∀ X0 : G, (M.op X0 (M.op x (M.op y (M.op x y)))) = X0 := by
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
  have eq176 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X1))) ≠ (M.op X0 (M.op X1 (M.op X0 X1))) ∨ (k (M.op X0 (M.op X1 (M.op X0 X1))) X2) = (M.op X2 (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 (M.op X1 (M.op X0 X1))) X2
       have i₂ := eq16 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 (M.op X0 (M.op X1 (M.op X0 X1))) X2
       grind)
    | (have r₁ := eq13 (M.op X1 (M.op X2 (M.op X1 X2))) X1
       have r₂ := eq16 (M.op X1 (M.op X2 (M.op X1 X2))) X1 X2
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X1 (M.op X0 X1))) X2) = (M.op X2 (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq179 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq181 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X1 (M.op X0 X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X0 X1 X2
       have i₂ := eq16 X2 X0 X1
       grind)
    | exact superpose eq16 eq180
    | exact resolve eq180 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq339 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq727 : x ≠ (M.op x y) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq728 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq735 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq736 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq744 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq784 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq744 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq794 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq784 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq784 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq784 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq842 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (M.op X1 (M.op X2 (M.op X1 X2)))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq339 (M.op X1 (M.op X2 (M.op X1 X2))) X0
       have i₂ := eq181 X1 X2 (σ X0)
       grind)
    | exact superpose eq181 eq339
    | exact resolve eq339 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq843 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (σ (M.op X1 (M.op X2 (M.op X1 X2)))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39 X0 (M.op X1 (M.op X2 (M.op X1 X2)))
       have i₂ := eq181 X1 X2 (τ X0)
       grind)
    | exact superpose eq181 eq39
    | exact resolve eq39 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq857 : ∀ X0 X1 X2 : G, (k (σ (M.op X1 (M.op X2 (M.op X1 X2)))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq843 X0 X1 X2
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq843
    | exact resolve eq843 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq858 : ∀ X0 X1 X2 : G, (k (τ (M.op X1 (M.op X2 (M.op X1 X2)))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq842 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq842
    | exact resolve eq842 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq1204 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq735
       grind)
    | exact superpose eq735 eq41
    | exact resolve eq41 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq735
  have eq1206 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1204
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1204
    | exact resolve eq1204 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204
  have eq1208 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1206
    | exact resolve eq1206 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206
  have eq1381 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 (M.op X0 X1)))) ≠ (σ (M.op X0 (M.op X1 (M.op X0 X1)))) ∨ (k (σ (M.op X0 (M.op X1 (M.op X0 X1)))) X2) = (M.op X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq794 (σ (M.op X0 (M.op X1 (M.op X0 X1)))) X2
       have i₂ := eq857 (σ (M.op X0 (M.op X1 (M.op X0 X1)))) X0 X1
       grind)
    | exact superpose eq857 eq794
    | (have j0 := eq794 (σ (M.op X0 (M.op X1 (M.op X0 X1)))) X2
       grind)
    | (have r₁ := eq794 (σ (M.op X1 (M.op X2 (M.op X1 X2)))) X1
       have r₂ := eq857 (σ (M.op X1 (M.op X2 (M.op X1 X2)))) X1 X2
       grind)
    | exact resolve eq794 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1393 : ∀ X0 X1 X2 : G, (k (σ (M.op X0 (M.op X1 (M.op X0 X1)))) X2) = (M.op X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1381 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381
  have eq1402 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1393 X0 X1 X2
       have i₂ := eq857 X2 X0 X1
       grind)
    | exact superpose eq857 eq1393
    | exact resolve eq1393 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857 eq1393
  have eq1443 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X1 (M.op X0 X1)))) ≠ (τ (M.op X0 (M.op X1 (M.op X0 X1)))) ∨ (k (τ (M.op X0 (M.op X1 (M.op X0 X1)))) X2) = (M.op X2 (τ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq794 (τ (M.op X0 (M.op X1 (M.op X0 X1)))) X2
       have i₂ := eq858 (τ (M.op X0 (M.op X1 (M.op X0 X1)))) X0 X1
       grind)
    | exact superpose eq858 eq794
    | (have j0 := eq794 (τ (M.op X0 (M.op X1 (M.op X0 X1)))) X2
       grind)
    | (have r₁ := eq794 (τ (M.op X1 (M.op X2 (M.op X1 X2)))) X1
       have r₂ := eq858 (τ (M.op X1 (M.op X2 (M.op X1 X2)))) X1 X2
       grind)
    | exact resolve eq794 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1455 : ∀ X0 X1 X2 : G, (k (τ (M.op X0 (M.op X1 (M.op X0 X1)))) X2) = (M.op X2 (τ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1443 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1443
  have eq1464 : ∀ X0 X1 X2 : G, (M.op X2 (τ (M.op X0 (M.op X1 (M.op X0 X1))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1455 X0 X1 X2
       have i₂ := eq858 X2 X0 X1
       grind)
    | exact superpose eq858 eq1455
    | exact resolve eq1455 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858 eq1455
  have eq2627 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1208 eq736
    | exact resolve eq736 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736 eq1208
  have eq2637 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq2627
       have r₂ := eq27
       grind)
    | exact resolve eq2627 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2627
  have eq2656 : ∀ X0 : G, (M.op X0 (τ (M.op (σ x) (M.op (σ x) (σ x))))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq2637 eq1464
    | exact resolve eq1464 eq2637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2660 : ∀ X0 : G, (M.op X0 (τ (M.op (σ x) (σ x)))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq2637 eq2656
    | exact resolve eq2656 eq2637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2656
  have eq2673 : ∀ X0 : G, (M.op X0 (τ (σ x))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq2637 eq2660
    | exact resolve eq2660 eq2637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2637 eq2660
  have eq2686 : ∀ X0 : G, x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq30 eq2673
    | exact resolve eq2673 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2673
  have eq2915 : x ≠ x ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have j0 := eq2686 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2686
  have eq2916 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2915
  have eq2953 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op X0 x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq2916
       grind)
    | exact superpose eq2916 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq2916
       grind)
    | exact resolve eq13 eq2916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2954 : ∀ X0 : G, (M.op X0 (M.op x (M.op x x))) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x
       have i₂ := eq2916
       grind)
    | exact superpose eq2916 eq16
    | exact resolve eq16 eq2916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2955 : x ≠ x ∨ x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq2916
       grind)
    | exact superpose eq2916 eq28
    | (have r₁ := eq28 x x
       have r₂ := eq2916
       grind)
    | (have r₁ := eq28 x y
       have r₂ := eq2916
       grind)
    | (have r₁ := eq28 (σ x) (σ y)
       have r₂ := eq2916
       grind)
    | exact resolve eq28 eq2916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2957 : ∀ X0 : G, (k (M.op x (M.op x x)) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq181 x x X0
       have i₂ := eq2916
       grind)
    | exact superpose eq2916 eq181
    | exact resolve eq181 eq2916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq2968 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2955
  have eq2969 : ∀ X0 : G, (k x X0) = (M.op X0 x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2953 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2953
  have eq2981 : ∀ X0 : G, (k (M.op x x) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2916 eq2957
    | exact resolve eq2957 eq2916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2957
  have eq2983 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2916 eq2954
    | exact resolve eq2954 eq2916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2916 eq2954
  have eq2994 : ∀ X0 : G, (k (k x x) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2969 eq2981
    | exact resolve eq2981 eq2969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2981
  have eq2996 : ∀ X0 : G, (M.op X0 (k x x)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2969 eq2983
    | exact resolve eq2983 eq2969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2969 eq2983
  have eq3007 : ∀ X0 : G, (k x X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2968 eq2994
    | exact resolve eq2994 eq2968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2994
  have eq3009 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2968 eq2996
    | exact resolve eq2996 eq2968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2996
  have eq3016 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq2968
       grind)
    | exact superpose eq2968 eq40
    | exact resolve eq40 eq2968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2968
  have eq3026 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3016
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3016
    | exact resolve eq3016 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3016
  have eq3038 : ∀ X0 : G, (σ (τ X0)) = (k (σ x) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq39 X0 x
       have i₂ := eq3007 (τ X0)
       grind)
    | exact superpose eq3007 eq39
    | exact resolve eq39 eq3007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq3007
  have eq3055 : ∀ X0 : G, (σ (τ X0)) = (k (σ x) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3038 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3038
    | (have j0 := eq3038 X0
       grind)
    | exact resolve eq3038 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3038
  have eq3061 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3055 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq3055
    | exact resolve eq3055 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3055
  have eq3065 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 x) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq28 X0 x
       have i₂ := eq3009 X0
       grind)
    | exact superpose eq3009 eq28
    | (have j0 := eq28 X0 x
       grind)
    | (have r₁ := eq28 X0 x
       have r₂ := eq3009 X0
       grind)
    | (have r₁ := eq28 x y
       have r₂ := eq3009 X0
       grind)
    | (have r₁ := eq28 (σ x) (σ y)
       have r₂ := eq3009 X0
       grind)
    | exact resolve eq28 eq3009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3009
  have eq3081 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3065 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3065
  have eq3089 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq3026 eq794
    | (have j0 := eq794 (σ x) X0
       grind)
    | (have r₁ := eq794 (σ x) x
       have r₂ := eq3026
       grind)
    | exact resolve eq794 eq3026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794 eq3026
  have eq3097 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3089 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3089
  have eq3098 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq3061 eq3097
    | exact resolve eq3097 eq3061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3061 eq3097
  have eq3226 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq3098 eq28
    | (have j0 := eq28 X0 (σ x)
       grind)
    | (have r₁ := eq28 X0 (σ x)
       have r₂ := eq3098 X0
       grind)
    | (have r₁ := eq28 x y
       have r₂ := eq3098 X0
       grind)
    | (have r₁ := eq28 (σ x) (σ y)
       have r₂ := eq3098 X0
       grind)
    | exact resolve eq28 eq3098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3098
  have eq3242 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3226 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3226
  have eq4064 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3081 y
       grind)
    | exact superpose eq3081 eq18
    | (have j1 := eq3081 y
       grind)
    | exact resolve eq18 eq3081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3081
  have eq4272 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq4064
       grind)
    | exact superpose eq4064 eq40
    | exact resolve eq40 eq4064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq4064
  have eq4276 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4272
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4272
    | exact resolve eq4272 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4272
  have eq4278 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq4276
    | exact resolve eq4276 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4276
  have eq4451 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3242 eq26
    | (have j1 := eq3242 (σ y)
       grind)
    | exact resolve eq26 eq3242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3242
  have eq4598 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4278 eq4451
    | exact resolve eq4451 eq4278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4278 eq4451
  have eq4643 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4598
       have r₂ := eq27
       grind)
    | exact resolve eq4598 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4598
  have eq4654 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4643 eq176
    | exact resolve eq176 eq4643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq4673 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4643 eq728
    | (have r₁ := eq728
       have r₂ := eq4643
       grind)
    | exact resolve eq728 eq4643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728 eq4643
  have eq4689 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq4673
  have eq4708 : ∀ X0 : G, (M.op X0 (M.op (σ x) (k (σ x) (σ y)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4689 eq4654
    | exact resolve eq4654 eq4689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4654
  have eq4727 : ∀ X0 : G, (M.op X0 (τ (M.op (σ y) (M.op (σ x) (k (σ x) (σ y)))))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4689 eq1464
    | exact resolve eq1464 eq4689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1464 eq4689
  have eq4730 : ∀ X0 : G, (M.op X0 (τ (σ y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4708 eq4727
    | exact resolve eq4727 eq4708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4708 eq4727
  have eq4746 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq32 eq4730
    | exact resolve eq4730 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq4730
  have eq4877 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4746 x
       grind)
    | exact superpose eq4746 eq18
    | (have j1 := eq4746 x
       grind)
    | exact resolve eq18 eq4746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4746
  have eq4882 : x = (M.op x y) := by grind
  clear eq4877
  have eq4889 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq4882
       grind)
    | exact superpose eq4882 eq22
    | exact resolve eq22 eq4882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq4892 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op y (M.op x y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq4882
       grind)
    | exact superpose eq4882 eq175
    | exact resolve eq175 eq4882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq4913 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq727
       have i₂ := eq4882
       grind)
    | exact superpose eq4882 eq727
    | (have r₁ := eq727
       have r₂ := eq4882
       grind)
    | exact resolve eq727 eq4882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727 eq4882
  have eq4931 : (k (M.op x y) y) = (M.op y (M.op x y)) := by grind
  clear eq4913
  have eq4950 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (k (M.op x y) y))) = X0 := by
    intro X0
    first
    | exact superpose eq4931 eq4892
    | exact resolve eq4892 eq4931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4892
  have eq4952 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4889 eq20
    | exact resolve eq20 eq4889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4889
  have eq5479 : ∀ X0 : G, (M.op X0 (σ (M.op y (M.op (M.op x y) (k (M.op x y) y))))) = X0 := by
    intro X0
    first
    | exact superpose eq4931 eq1402
    | exact resolve eq1402 eq4931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402 eq4931
  have eq5482 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq4950 eq5479
    | exact resolve eq5479 eq4950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4950 eq5479
  have eq5532 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5482 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5482
    | (have j0 := eq5482 X0
       grind)
    | exact resolve eq5482 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq5482
  have eq5665 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5532 eq26
    | (have j1 := eq5532 (σ x)
       grind)
    | exact resolve eq26 eq5532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq5532
  have eq5676 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq5665 eq27
    | exact resolve eq27 eq5665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq5665
  have eq5736 : False := by grind
  exact eq5736

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_pyx_y_pxy_Equation452 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
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
  clear eq36
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
  have eq114 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47
    | (have j0 := eq47 x
       grind)
    | exact resolve eq47 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
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
  have eq174 : ∀ X0 : G, (M.op X0 (M.op x (M.op y (M.op x y)))) = X0 := by
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
  have eq175 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : x ≠ (M.op x y) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = (M.op (M.op X1 (M.op X2 (M.op X1 X2))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X1 (M.op X2 (M.op X1 X2)))
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 X0 (M.op X1 (M.op X2 (M.op X1 X2)))
       grind)
    | (have r₁ := eq13 X0 (M.op X1 (M.op X2 (M.op X1 X2)))
       have r₂ := eq16 X0 X1 X2
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = (M.op (M.op X1 (M.op X2 (M.op X1 X2))) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq180 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq961 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 (M.op X2 (M.op X1 X2))) = (M.op (M.op X1 (M.op X2 (M.op X1 X2))) X0) ∨ (k (M.op X1 (M.op X2 (M.op X1 X2))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op X2 (M.op X1 X2))) X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq12
    | (have j0 := eq12 (M.op X1 (M.op X2 (M.op X1 X2))) X0
       grind)
    | (have r₁ := eq12 (M.op X1 (M.op X2 (M.op X1 X2))) X0
       have r₂ := eq16 X0 X1 X2
       grind)
    | exact resolve eq12 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq970 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 X2))) = (M.op (M.op X1 (M.op X2 (M.op X1 X2))) X0) ∨ (k (M.op X1 (M.op X2 (M.op X1 X2))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq961 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961
  have eq975 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 X2))) = (k X0 (M.op X1 (M.op X2 (M.op X1 X2)))) ∨ (k (M.op X1 (M.op X2 (M.op X1 X2))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq970 X0 X1 X2
       have i₂ := eq181 X0 X1 X2
       grind)
    | exact superpose eq181 eq970
    | (have j0 := eq970 X0 X1 X2
       grind)
    | exact resolve eq970 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq980 : (M.op x y) = (k x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq981 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1006 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1007 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1008 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1006 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006
  have eq1027 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq980
       grind)
    | exact superpose eq980 eq40
    | exact resolve eq40 eq980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1028 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1027
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1027
    | exact resolve eq1027 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq1030 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1028
    | exact resolve eq1028 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028
  have eq1038 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1030 eq981
    | exact resolve eq981 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1045 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1038
       have r₂ := eq27
       grind)
    | exact resolve eq1038 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038
  have eq1050 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1045 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1045
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1045
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1045
       grind)
    | exact resolve eq12 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1054 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq1050
  have eq1057 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1054
    | exact resolve eq1054 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054
  have eq1058 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq1057
  have eq1066 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1058 eq1030
    | exact resolve eq1030 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030
  have eq1069 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1058 eq90
    | exact resolve eq90 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq1058
  have eq1072 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1066
  have eq1076 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq1069
    | exact resolve eq1069 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq1079 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq980 eq1076
    | exact resolve eq1076 eq980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980 eq1076
  have eq1085 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq1072
       grind)
    | exact superpose eq1072 eq16
    | exact resolve eq16 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1088 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1085 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1085
    | (have j0 := eq1085 X0
       grind)
    | exact resolve eq1085 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq1095 : y ≠ y ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1079
       grind)
    | exact superpose eq1079 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1079
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1079
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1079
       grind)
    | exact resolve eq13 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079
  have eq1097 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1095
  have eq1100 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1097
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1097
    | exact resolve eq1097 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097
  have eq1120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1100
       grind)
    | exact superpose eq1100 eq39
    | exact resolve eq39 eq1100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq1121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1120
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1120
    | exact resolve eq1120 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1123 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1121
    | exact resolve eq1121 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121
  have eq1197 : ∀ X0 : G, (M.op X0 x) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1088 eq174
    | exact resolve eq174 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq1204 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 x) = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq1197 X0
       grind)
    | exact superpose eq1197 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq1197 X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1197 X0
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1197 X0
       grind)
    | exact resolve eq13 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1208 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1204 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204
  have eq1266 : x = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1197 x
       have i₂ := eq1208 x
       grind)
    | exact superpose eq1208 eq1197
    | exact resolve eq1197 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197 eq1208
  have eq1267 : x = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1266
  have eq1295 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq1267
       grind)
    | exact superpose eq1267 eq39
    | exact resolve eq39 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1267
  have eq1298 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1295
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1295
    | exact resolve eq1295 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295
  have eq1303 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1298 eq1008
    | (have j0 := eq1008 (σ x)
       grind)
    | (have r₁ := eq1008 (σ x)
       have r₂ := eq1298
       grind)
    | exact resolve eq1008 eq1298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008 eq1298
  have eq1304 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1303
  have eq1310 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ x)))) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1304 eq16
    | exact resolve eq16 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1313 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1304 eq1310
    | exact resolve eq1310 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310
  have eq1314 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1304 eq1313
    | exact resolve eq1313 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304 eq1313
  have eq1470 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1123 eq1007
    | (have j0 := eq1007 (σ y) (σ x)
       grind)
    | exact resolve eq1007 eq1123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1479 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq1314 (σ y)
       grind)
    | (have r₁ := eq1470
       have r₂ := eq1314 x
       grind)
    | exact resolve eq1470 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314 eq1470
  have eq1483 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1479
    | exact resolve eq1479 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479
  have eq1484 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1483
  have eq1488 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1484 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1484
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1484
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1484
       grind)
    | exact resolve eq13 eq1484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484
  have eq1490 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1488
  have eq1493 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1490
    | exact resolve eq1490 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1490
  have eq1496 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1123 eq1493
    | exact resolve eq1493 eq1123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123 eq1493
  have eq1497 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1496
       have r₂ := eq27
       grind)
    | exact resolve eq1496 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496
  have eq1501 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1497 eq175
    | exact resolve eq175 eq1497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1537 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f1537_15 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
      intro X0
      grind
    have f1537_23 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
      intro X0 X1 X2
      grind
    have f1537_24 : X0 ≠ (M.op X0 (σ y)) := by grind
    have f1537_25 : y ≠ (M.op x y) := by grind
    have f1537_26 : x ≠ (M.op x y) := by grind
    have f1537_27 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ x = (M.op x y) := by
      intro X0
      first
      | (have j0 := f1537_15 X0
         grind)
      | (have r₁ := f1537_15 X0
         have r₂ := f1537_25
         grind)
      | exact resolve f1537_15 f1537_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1537_28 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 := by
      intro X0
      first
      | (have j0 := f1537_27 X0
         grind)
      | (have r₁ := f1537_27 X0
         have r₂ := f1537_26
         grind)
      | exact resolve f1537_27 f1537_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1537_47 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
      intro X0
      first
      | (have i₁ := f1537_23 X0 (σ y) (σ x)
         have i₂ := f1537_28 (σ y)
         grind)
      | exact superpose f1537_28 f1537_23
      | exact resolve f1537_23 f1537_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1537_55 : X0 ≠ X0 := by
      first
      | (have i₁ := f1537_24
         have i₂ := f1537_47 X0
         grind)
      | exact superpose f1537_47 f1537_24
      | (have r₁ := f1537_24
         have r₂ := f1537_47 X0
         grind)
      | exact resolve f1537_24 f1537_47
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1537_56 : False := by grind
    exact f1537_56
  clear eq1501
  have eq1574 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1537 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1537 X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1537 X0
       grind)
    | exact resolve eq13 eq1537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1582 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1574 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1574
  have eq1634 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1582 eq1537
    | exact resolve eq1537 eq1582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537 eq1582
  have eq1635 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1634
  have eq1686 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1635 eq152
    | exact resolve eq152 eq1635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1635
  have eq1692 : y = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq1686
    | exact resolve eq1686 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1686
  have eq1698 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1007 y y
       have i₂ := eq1692
       grind)
    | exact superpose eq1692 eq1007
    | (have j0 := eq1007 y y
       grind)
    | (have r₁ := eq1007 y y
       have r₂ := eq1692
       grind)
    | exact resolve eq1007 eq1692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1692
  have eq1699 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1698
  have eq1700 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1699
  have eq1707 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq1700
       grind)
    | exact superpose eq1700 eq16
    | exact resolve eq16 eq1700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1710 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1700 eq1707
    | exact resolve eq1707 eq1700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1707
  have eq1712 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1700 eq1710
    | exact resolve eq1710 eq1700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1700 eq1710
  have eq1725 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1712 x
       grind)
    | exact superpose eq1712 eq18
    | (have j1 := eq1712 x
       grind)
    | exact resolve eq18 eq1712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1712
  have eq1730 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1725
  have eq1736 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1730
       grind)
    | exact superpose eq1730 eq18
    | exact resolve eq18 eq1730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1737 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1730
       grind)
    | exact superpose eq1730 eq24
    | exact resolve eq24 eq1730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1740 : ∀ X0 : G, (M.op X0 (M.op x (M.op (M.op x y) (M.op x y)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq1730
       grind)
    | exact superpose eq1730 eq174
    | exact resolve eq174 eq1730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1754 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1737
    | exact resolve eq1737 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1737
  have eq1784 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1736
       have i₂ := eq11 x sF0
       grind)
    | exact superpose eq11 eq1736
    | (have j1 := eq11 x (M.op x y)
       grind)
    | exact resolve eq1736 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1794 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have j1 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq1784
       have r₂ := eq12 y x
       grind)
    | (have r₁ := eq1784
       have r₂ := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq1784
       have r₂ := eq12 (M.op x y) x
       grind)
    | exact resolve eq1784 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1784
  have eq1795 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1736 eq1794
    | exact resolve eq1794 eq1736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1794
  have eq1796 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq1795
  have eq1797 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1796 eq35
    | exact resolve eq35 eq1796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1796
  have eq1801 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1797
    | exact resolve eq1797 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1797
  have eq1803 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1754 eq1801
    | exact resolve eq1801 eq1754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1801
  have eq1808 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1803 eq981
    | exact resolve eq981 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq1936 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1808 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1808
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1808
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1808
       grind)
    | exact resolve eq13 eq1808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1937 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1808 eq16
    | exact resolve eq16 eq1808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1808
  have eq1938 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1936
  have eq1945 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq1937
    | (have j0 := eq1937 X0
       grind)
    | exact resolve eq1937 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1937
  have eq1946 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1938
    | exact resolve eq1938 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1938
  have eq1953 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1946 eq114
    | exact resolve eq114 eq1946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq1946
  have eq1963 : (k (M.op x y) x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1497 eq1953
    | exact resolve eq1953 eq1497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497 eq1953
  have eq2210 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 X2))) ≠ (k X0 (M.op X1 (M.op X2 (M.op X1 X2)))) ∨ (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = (k (M.op X1 (M.op X2 (M.op X1 X2))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 (M.op X2 (M.op X1 X2))) X0
       have i₂ := eq181 X0 X1 X2
       grind)
    | exact superpose eq181 eq13
    | (have j0 := eq13 (M.op X1 (M.op X2 (M.op X1 X2))) X0
       grind)
    | exact resolve eq13 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2248 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X2 (M.op X1 X2))) X0) = X0 ∨ (M.op X1 (M.op X2 (M.op X1 X2))) ≠ (k X0 (M.op X1 (M.op X2 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2210 X0 X1 X2
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq2210
    | (have j0 := eq2210 X0 X1 X2
       grind)
    | exact resolve eq2210 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2210
  have eq2274 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X2 (M.op X1 X2))) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq2248 X0 X1 X2
       have j1 := eq975 X0 X1 X2
       grind)
    | (have r₁ := eq2248 X0 X1 X2
       have r₂ := eq975 X0 X1 X2
       grind)
    | (have r₁ := eq2248 (M.op X1 (M.op X2 (M.op X1 X2))) X1 X2
       have r₂ := eq975 (M.op X1 (M.op X2 (M.op X1 X2))) X1 X2
       grind)
    | exact resolve eq2248 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975 eq2248
  have eq3170 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1945 eq175
    | exact resolve eq175 eq1945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq1945
  have eq3205 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3170 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq3170 X0
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3170 X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq3170 X0
       grind)
    | exact resolve eq13 eq3170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3229 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3205 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3205
  have eq3320 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3229 eq3170
    | exact resolve eq3170 eq3229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3170 eq3229
  have eq3325 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3320
  have eq3408 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3325 eq141
    | exact resolve eq141 eq3325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq3325
  have eq3419 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq3408
    | exact resolve eq3408 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3408
  have eq3427 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1007 x x
       have i₂ := eq3419
       grind)
    | exact superpose eq3419 eq1007
    | (have j0 := eq1007 x x
       grind)
    | (have r₁ := eq1007 x x
       have r₂ := eq3419
       grind)
    | exact resolve eq1007 eq3419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3419
  have eq3428 : x ≠ x ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3427
  have eq3429 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3428
  have eq3441 : ∀ X0 : G, (k X0 (M.op x (M.op x x))) = (M.op (M.op x (M.op x x)) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq181 X0 x x
       have i₂ := eq3429
       grind)
    | exact superpose eq3429 eq181
    | exact resolve eq181 eq3429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3453 : ∀ X0 : G, (k X0 (M.op x x)) = (M.op (M.op x x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3429 eq3441
    | exact resolve eq3441 eq3429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3441
  have eq3456 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3429 eq3453
    | exact resolve eq3453 eq3429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3429 eq3453
  have eq4263 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1736
       have i₂ := eq3456 sF0
       grind)
    | exact superpose eq3456 eq1736
    | exact resolve eq1736 eq3456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3456
  have eq4340 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4263
  have eq4430 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4340 eq1963
    | exact resolve eq1963 eq4340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1963 eq4340
  have eq4438 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4430
  have eq4450 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4438 eq14
    | exact resolve eq14 eq4438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4438
  have eq4452 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4450
    | exact resolve eq4450 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4450
  have eq4455 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4452
       have r₂ := eq27
       grind)
    | exact resolve eq4452 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4452
  have eq4458 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4455 eq27
    | exact resolve eq27 eq4455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4455
  have eq4470 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4458
       have r₂ := eq1754
       grind)
    | exact resolve eq4458 eq1754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1754 eq4458
  have eq4475 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4470 eq179
    | (have r₁ := eq179
       have r₂ := eq4470
       grind)
    | exact resolve eq179 eq4470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq4479 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq4475
  have eq4481 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1803 eq4479
    | exact resolve eq4479 eq1803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803 eq4479
  have eq4493 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4481 eq16
    | exact resolve eq16 eq4481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4495 : ∀ X0 : G, (k X0 (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4481 eq181
    | exact resolve eq181 eq4481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq4507 : ∀ X0 : G, (k X0 (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq4495
    | (have j0 := eq4495 X0
       grind)
    | exact resolve eq4495 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4495
  have eq4509 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq4493
    | (have j0 := eq4493 X0
       grind)
    | exact resolve eq4493 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4493
  have eq4513 : ∀ X0 : G, (k X0 (M.op (σ y) (σ x))) = (M.op (M.op (σ y) (σ x)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4470 eq4507
    | exact resolve eq4507 eq4470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4507
  have eq4515 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ x))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4470 eq4509
    | exact resolve eq4509 eq4470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4470 eq4509
  have eq4518 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4481 eq4513
    | exact resolve eq4513 eq4481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4513
  have eq4520 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4481 eq4515
    | exact resolve eq4515 eq4481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4481 eq4515
  have eq4737 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4518 eq4520
    | exact resolve eq4520 eq4518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4518 eq4520
  have eq4740 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4737
  have eq4871 : (τ (σ y)) = (k (τ (σ y)) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4740 eq152
    | exact resolve eq152 eq4740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq4740
  have eq4883 : y = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq4871
    | exact resolve eq4871 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq4871
  have eq4886 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1730 eq4883
    | exact resolve eq4883 eq1730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1730 eq4883
  have eq4978 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4886 eq1007
    | (have j0 := eq1007 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq1007 (M.op x y) (M.op x y)
       have r₂ := eq4886
       grind)
    | exact resolve eq1007 eq4886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4886
  have eq4979 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq4978
  have eq4980 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq4979
  have eq5384 : ∀ X0 : G, (M.op X0 (M.op x (M.op x y))) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4980 eq1740
    | exact resolve eq1740 eq4980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1740 eq4980
  have eq5395 : ∀ X0 : G, (M.op X0 (M.op x (M.op x y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq5384 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5384
  have eq5405 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1736 eq5395
    | exact resolve eq5395 eq1736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5395
  have eq5439 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5405 eq1736
    | exact resolve eq1736 eq5405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1736 eq5405
  have eq5474 : x = (M.op x y) := by grind
  clear eq5439
  have eq5491 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq5474
       grind)
    | exact superpose eq5474 eq22
    | exact resolve eq22 eq5474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq5494 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op y (M.op x y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq5474
       grind)
    | exact superpose eq5474 eq174
    | exact resolve eq174 eq5474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq5495 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq178
       have i₂ := eq5474
       grind)
    | exact superpose eq5474 eq178
    | (have r₁ := eq178
       have r₂ := eq5474
       grind)
    | exact resolve eq178 eq5474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq5474
  have eq5499 : (k (M.op x y) y) = (M.op y (M.op x y)) := by grind
  clear eq5495
  have eq5500 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (k (M.op x y) y))) = X0 := by
    intro X0
    first
    | exact superpose eq5499 eq5494
    | exact resolve eq5494 eq5499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5494
  have eq5502 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5491 eq20
    | exact resolve eq20 eq5491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5491
  have eq5662 : ∀ X0 : G, (k (M.op y (M.op (M.op x y) (k (M.op x y) y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq5499 eq2274
    | exact resolve eq2274 eq5499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274 eq5499
  have eq5663 : ∀ X0 : G, (k y X0) = X0 := by
    intro X0
    first
    | exact superpose eq5500 eq5662
    | exact resolve eq5662 eq5500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5500 eq5662
  have eq5751 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq5663 y
       grind)
    | exact superpose eq5663 eq40
    | exact resolve eq40 eq5663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq5663
  have eq5769 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq5751
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5751
    | exact resolve eq5751 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq5751
  have eq5838 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq5769 eq1007
    | (have j0 := eq1007 (σ y) (σ y)
       grind)
    | (have r₁ := eq1007 (σ y) (σ y)
       have r₂ := eq5769
       grind)
    | exact resolve eq1007 eq5769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007 eq5769
  have eq5839 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5838
  have eq5840 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5839
  have eq5945 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq5840 eq16
    | exact resolve eq16 eq5840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5960 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq5840 eq5945
    | exact resolve eq5945 eq5840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5945
  have eq5965 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq5840 eq5960
    | exact resolve eq5960 eq5840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5840 eq5960
  have eq5997 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5965 eq26
    | (have j1 := eq5965 (σ x)
       grind)
    | exact resolve eq26 eq5965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq5965
  have eq6020 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq5997 eq27
    | exact resolve eq27 eq5997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq5997
  have eq6029 : False := by grind
  exact eq6029

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pxy_x_pyx_Equation452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
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
  have eq174 : ∀ X0 : G, (M.op X0 (M.op x (M.op y (M.op x y)))) = X0 := by
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
  have eq175 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : x ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
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
  have eq978 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq979 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1004 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1005 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1006 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1004 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq1024 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq978
       grind)
    | exact superpose eq978 eq39
    | exact resolve eq39 eq978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq1025 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1024
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1024
    | exact resolve eq1024 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1027 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1025
    | exact resolve eq1025 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025
  have eq1035 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1027 eq979
    | exact resolve eq979 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979 eq1027
  have eq1042 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1035
       have r₂ := eq27
       grind)
    | exact resolve eq1035 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035
  have eq1047 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1042 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq1042
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1042
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq1042
       grind)
    | exact resolve eq13 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq1051 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq1047
  have eq1057 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1051 eq141
    | exact resolve eq141 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq1051
  have eq1060 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1057
    | exact resolve eq1057 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1057
  have eq1063 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq1006 x
       grind)
    | (have r₁ := eq1060
       have r₂ := eq1006 x
       grind)
    | exact resolve eq1060 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060
  have eq1067 : x ≠ x ∨ x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq1063
       grind)
    | exact superpose eq1063 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq1063
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1063
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1063
       grind)
    | exact resolve eq13 eq1063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1068 : ∀ X0 : G, (M.op X0 (M.op x (M.op x x))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x
       have i₂ := eq1063
       grind)
    | exact superpose eq1063 eq16
    | exact resolve eq16 eq1063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1071 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1067
  have eq1073 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1063 eq1068
    | exact resolve eq1068 eq1063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq1074 : ∀ X0 : G, (M.op X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1063 eq1073
    | exact resolve eq1073 eq1063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063 eq1073
  have eq1076 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq1071
       grind)
    | exact superpose eq1071 eq39
    | exact resolve eq39 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1071
  have eq1079 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1076
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1076
    | exact resolve eq1076 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq1083 : ∀ X0 : G, X0 ≠ X0 ∨ (k x X0) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq1074 X0
       grind)
    | exact superpose eq1074 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x X0
       have r₂ := eq1074 X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1074 X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1074 X0
       grind)
    | exact resolve eq13 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074
  have eq1087 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1083 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1095 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1079 eq1006
    | (have j0 := eq1006 (σ x)
       grind)
    | (have r₁ := eq1006 (σ x)
       have r₂ := eq1079
       grind)
    | exact resolve eq1006 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079
  have eq1096 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1095
  have eq1103 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ x)))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1096 eq16
    | exact resolve eq16 eq1096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1107 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ x))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1096 eq1103
    | exact resolve eq1103 eq1096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1108 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1096 eq1107
    | exact resolve eq1107 eq1096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096 eq1107
  have eq1111 : ∀ X0 : G, X0 ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1108 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) X0
       have r₂ := eq1108 X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1108 X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1108 X0
       grind)
    | exact resolve eq13 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108
  have eq1115 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1111 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111
  have eq1132 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1087 y
       grind)
    | exact superpose eq1087 eq18
    | (have j1 := eq1087 y
       grind)
    | exact resolve eq18 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq1175 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1132
       grind)
    | exact superpose eq1132 eq40
    | exact resolve eq40 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132
  have eq1176 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1175
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1175
    | exact resolve eq1175 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175
  have eq1178 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1176
    | exact resolve eq1176 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176
  have eq1219 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1115 eq26
    | (have j1 := eq1115 (σ y)
       grind)
    | exact resolve eq26 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1253 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1178 eq1219
    | exact resolve eq1219 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178 eq1219
  have eq1263 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1253
       have r₂ := eq27
       grind)
    | exact resolve eq1253 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253
  have eq1269 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1263 eq175
    | exact resolve eq175 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq1263
  have eq1294 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f1294_13 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ x = (M.op x y) := by
      intro X0
      grind
    have f1294_20 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
      intro X0 X1 X2
      grind
    have f1294_21 : X0 ≠ (M.op X0 (σ y)) := by grind
    have f1294_22 : x ≠ (M.op x y) := by grind
    have f1294_23 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 := by
      intro X0
      first
      | (have j0 := f1294_13 X0
         grind)
      | (have r₁ := f1294_13 X0
         have r₂ := f1294_22
         grind)
      | exact resolve f1294_13 f1294_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1294_50 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
      intro X0
      first
      | (have i₁ := f1294_20 X0 (σ y) (σ x)
         have i₂ := f1294_23 (σ y)
         grind)
      | exact superpose f1294_23 f1294_20
      | exact resolve f1294_20 f1294_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1294_58 : X0 ≠ X0 := by
      first
      | (have i₁ := f1294_21
         have i₂ := f1294_50 X0
         grind)
      | exact superpose f1294_50 f1294_21
      | (have r₁ := f1294_21
         have r₂ := f1294_50 X0
         grind)
      | exact resolve f1294_21 f1294_50
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1294_59 : False := by grind
    exact f1294_59
  clear eq1269
  have eq1325 : ∀ X0 : G, X0 ≠ X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1294 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) X0
       have r₂ := eq1294 X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1294 X0
       grind)
    | exact resolve eq13 eq1294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1334 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1325 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325
  have eq1369 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1334 eq1294
    | exact resolve eq1294 eq1334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294 eq1334
  have eq1370 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1369
  have eq1405 : (τ (σ y)) = (k (τ (σ y)) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1370 eq152
    | exact resolve eq152 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq1370
  have eq1408 : y = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq1405
    | exact resolve eq1405 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1405
  have eq1413 : y ≠ y ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1006 y
       have i₂ := eq1408
       grind)
    | exact superpose eq1408 eq1006
    | (have j0 := eq1006 y
       grind)
    | (have r₁ := eq1006 y
       have r₂ := eq1408
       grind)
    | exact resolve eq1006 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006 eq1408
  have eq1414 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq1413
  have eq1420 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq1414
       grind)
    | exact superpose eq1414 eq16
    | exact resolve eq16 eq1414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1424 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1414 eq1420
    | exact resolve eq1420 eq1414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420
  have eq1425 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1414 eq1424
    | exact resolve eq1424 eq1414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414 eq1424
  have eq1436 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1425 x
       grind)
    | exact superpose eq1425 eq18
    | (have j1 := eq1425 x
       grind)
    | exact resolve eq18 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1425
  have eq1443 : x = (M.op x y) := by grind
  clear eq1436
  have eq1591 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq1443
       grind)
    | exact superpose eq1443 eq22
    | exact resolve eq22 eq1443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1594 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op y (M.op x y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq1443
       grind)
    | exact superpose eq1443 eq174
    | exact resolve eq174 eq1443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq1595 : (M.op x y) ≠ (M.op x y) ∨ (k y (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq178
       have i₂ := eq1443
       grind)
    | exact superpose eq1443 eq178
    | (have r₁ := eq178
       have r₂ := eq1443
       grind)
    | exact resolve eq178 eq1443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq1443
  have eq1597 : (k y (M.op x y)) = (M.op y (M.op x y)) := by grind
  clear eq1595
  have eq1598 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (k y (M.op x y)))) = X0 := by
    intro X0
    first
    | exact superpose eq1597 eq1594
    | exact resolve eq1594 eq1597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594
  have eq1600 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1591 eq20
    | exact resolve eq20 eq1591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1591
  have eq1722 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) (k y (M.op x y))))) = X0 := by
    intro X0
    first
    | exact superpose eq1597 eq16
    | exact resolve eq16 eq1597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1597
  have eq1723 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq1598 eq1722
    | exact resolve eq1722 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1598 eq1722
  have eq1736 : ∀ X0 : G, X0 ≠ X0 ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq1723 X0
       grind)
    | exact superpose eq1723 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y X0
       have r₂ := eq1723 X0
       grind)
    | exact resolve eq13 eq1723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1745 : ∀ X0 : G, (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq1736 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1736
  have eq1790 : y = (k y y) := by
    first
    | (have i₁ := eq1723 y
       have i₂ := eq1745 y
       grind)
    | exact superpose eq1745 eq1723
    | exact resolve eq1723 eq1745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1723 eq1745
  have eq1826 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1790
       grind)
    | exact superpose eq1790 eq40
    | exact resolve eq40 eq1790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1790
  have eq1832 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1826
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1826
    | exact resolve eq1826 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1826
  have eq1869 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1832 eq1005
    | (have j0 := eq1005 (σ y) (σ y)
       grind)
    | (have r₁ := eq1005 (σ y) (σ y)
       have r₂ := eq1832
       grind)
    | exact resolve eq1005 eq1832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005 eq1832
  have eq1870 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1869
  have eq1871 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1870
  have eq1929 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq1871 eq16
    | exact resolve eq16 eq1871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1933 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq1871 eq1929
    | exact resolve eq1929 eq1871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1929
  have eq1935 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq1871 eq1933
    | exact resolve eq1933 eq1871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1871 eq1933
  have eq1952 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1935 eq26
    | (have j1 := eq1935 (σ x)
       grind)
    | exact resolve eq26 eq1935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1935
  have eq1965 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1952 eq27
    | exact resolve eq27 eq1952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1952
  have eq1967 : False := by grind
  exact eq1967

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_pxx_pxy_Equation452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op (M.op X2 (M.op X3 (M.op X2 X3))) X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X0 (M.op X2 (M.op X3 (M.op X2 X3)))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq33 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X1))) ≠ (M.op X0 (M.op X1 (M.op X0 X1))) ∨ (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op X2 (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 (M.op X1 (M.op X0 X1)))
       have i₂ := eq9 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op X2 (M.op X1 X2)))
       have r₂ := eq9 (M.op X1 (M.op X2 (M.op X1 X2))) X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op X2 (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq33 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq35 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 X1 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq70 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X2 (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (M.op X1 (M.op X2 (M.op X1 X2)))
       have i₂ := eq35 X1 X2 (σ X0)
       grind)
    | exact superpose eq35 eq30
    | exact resolve eq30 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op X2 (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (M.op X1 (M.op X2 (M.op X1 X2)))
       have i₂ := eq35 X1 X2 (τ X0)
       grind)
    | exact superpose eq35 eq17
    | exact resolve eq17 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X2 (M.op X1 X2))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq71
    | exact resolve eq71 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq73 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X2 (M.op X1 X2))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq70
    | exact resolve eq70 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq92 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (σ (M.op X1 (M.op X2 (M.op X1 X2))))
       have i₂ := eq72 (τ X0) X1 X2
       grind)
    | exact superpose eq72 eq17
    | exact resolve eq17 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq92 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq104 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 (M.op X2 (M.op X1 X2)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (τ (M.op X1 (M.op X2 (M.op X1 X2))))
       have i₂ := eq73 (σ X0) X1 X2
       grind)
    | exact superpose eq73 eq30
    | exact resolve eq30 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq112 : ∀ X0 X1 X2 : G, (k X0 (τ (τ (M.op X1 (M.op X2 (M.op X1 X2)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq104
    | exact resolve eq104 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq152 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))
       have i₂ := eq97 (τ X0) X1 X2
       grind)
    | exact superpose eq97 eq17
    | exact resolve eq17 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq157 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq152 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq152
    | exact resolve eq152 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq178 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq77
    | (have j0 := eq77 X2 X2
       grind)
    | exact resolve eq77 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq77 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq77 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq196 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq192 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq198 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq196 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq196 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq196 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq213 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2))))))
       have i₂ := eq157 (τ X0) X1 X2
       grind)
    | exact superpose eq157 eq17
    | exact resolve eq17 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq213 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq213
    | exact resolve eq213 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq451 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 (M.op X0 X1)))) ≠ (σ (M.op X0 (M.op X1 (M.op X0 X1)))) ∨ (k X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) = (M.op X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq198 (M.op X0 (M.op X1 (M.op X0 X1))) X2
       have i₂ := eq35 X0 X1 (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | exact superpose eq35 eq198
    | (have j0 := eq198 (M.op X0 (M.op X1 (M.op X0 X1))) X2
       grind)
    | exact resolve eq198 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq457 : ∀ X0 X1 X2 : G, (σ (τ (τ (M.op X0 (M.op X1 (M.op X0 X1)))))) ≠ (σ (τ (τ (M.op X0 (M.op X1 (M.op X0 X1)))))) ∨ (k X2 (σ (τ (τ (M.op X0 (M.op X1 (M.op X0 X1))))))) = (M.op X2 (σ (τ (τ (M.op X0 (M.op X1 (M.op X0 X1))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq198 (τ (τ (M.op X0 (M.op X1 (M.op X0 X1))))) X2
       have i₂ := eq112 (τ (τ (M.op X0 (M.op X1 (M.op X0 X1))))) X0 X1
       grind)
    | exact superpose eq112 eq198
    | (have j0 := eq198 (τ (τ (M.op X0 (M.op X1 (M.op X0 X1))))) X2
       grind)
    | exact resolve eq198 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq198
  have eq464 : ∀ X0 X1 X2 : G, (k X2 (σ (τ (τ (M.op X0 (M.op X1 (M.op X0 X1))))))) = (M.op X2 (σ (τ (τ (M.op X0 (M.op X1 (M.op X0 X1))))))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq457 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq470 : ∀ X0 X1 X2 : G, (k X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) = (M.op X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq451 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq476 : ∀ X0 X1 X2 : G, (k X2 (τ (M.op X0 (M.op X1 (M.op X0 X1))))) = (M.op X2 (τ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq464 X0 X1 X2
       have i₂ := eq11 (τ (M.op X0 (M.op X1 (M.op X0 X1))))
       grind)
    | exact superpose eq11 eq464
    | exact resolve eq464 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq482 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq470 X0 X1 X2
       have i₂ := eq72 X2 X0 X1
       grind)
    | exact superpose eq72 eq470
    | exact resolve eq470 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq470
  have eq487 : ∀ X0 X1 X2 : G, (M.op X2 (τ (M.op X0 (M.op X1 (M.op X0 X1))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq476 X0 X1 X2
       have i₂ := eq73 X2 X0 X1
       grind)
    | exact superpose eq73 eq476
    | exact resolve eq476 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq476
  have eq621 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op (τ (M.op X2 (M.op X3 (M.op X2 X3)))) X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X0 (τ (M.op X2 (M.op X3 (M.op X2 X3))))
       have i₂ := eq487 X2 X3 X0
       grind)
    | exact superpose eq487 eq9
    | exact resolve eq9 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq3035 : ∀ X0 X1 X2 X3 : G, (σ (k (τ X0) X3)) = (M.op (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) (σ X3)) ∨ (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) = (M.op (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) (σ X3)) ∨ (σ X3) = (M.op (σ X3) (σ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq178 X0 (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))) X3
       have i₂ := eq157 (τ X0) X1 X2
       grind)
    | exact superpose eq157 eq178
    | (have j0 := eq178 X0 (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))) X3
       grind)
    | exact resolve eq178 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq178
  have eq3119 : ∀ X0 X1 X2 X3 : G, (σ (k (τ X0) X3)) = (M.op X0 (σ X3)) ∨ (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) = (M.op (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) (σ X3)) ∨ (σ X3) = (M.op (σ X3) (σ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3035 X0 X1 X2 X3
       have i₂ := eq218 X0 X1 X2
       grind)
    | exact superpose eq218 eq3035
    | (have j0 := eq3035 X0 X1 X2 X3
       grind)
    | exact resolve eq3035 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3035
  have eq3147 : ∀ X0 X1 X2 X3 : G, (k X0 (σ X3)) = (M.op X0 (σ X3)) ∨ (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) = (M.op (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) (σ X3)) ∨ (σ X3) = (M.op (σ X3) (σ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3119 X0 X1 X2 X3
       have i₂ := eq17 X0 X3
       grind)
    | exact superpose eq17 eq3119
    | (have j0 := eq3119 X0 X1 X2 X3
       grind)
    | exact resolve eq3119 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq3119
  have eq3168 : ∀ X0 X1 X2 X3 : G, (k X0 (σ X3)) = (M.op X0 (σ X3)) ∨ (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) = (M.op (k X0 (σ (σ (σ (σ (M.op X1 (M.op X2 (M.op X1 X2)))))))) (σ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq3147 X0 X1 X2 X3
       have j1 := eq12 X0 (σ X3)
       grind)
    | (have r₁ := eq3147 X0 X1 X2 X3
       have r₂ := eq12 X0 (σ X3)
       grind)
    | exact resolve eq3147 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3147
  have eq3185 : ∀ X0 X3 : G, (k X0 (σ X3)) = (M.op X0 (σ X3)) ∨ (M.op X0 (σ X3)) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq3168 X0 x x X3
       have i₂ := eq218 X0 x x
       grind)
    | exact superpose eq218 eq3168
    | (have j0 := eq3168 X0 x x X3
       grind)
    | exact resolve eq3168 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq3168
  have eq3206 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3185 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3185
    | exact resolve eq3185 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3242 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3185 (σ X0) X1
       grind)
    | exact superpose eq3185 eq15
    | (have j1 := eq3185 (σ X0) X1
       grind)
    | exact resolve eq15 eq3185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3185
  have eq3322 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq3206 (τ X1) X0
       grind)
    | exact superpose eq3206 eq18
    | (have j1 := eq3206 (τ X1) X0
       grind)
    | exact resolve eq18 eq3206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3206
  have eq4798 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3322 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3322
    | exact resolve eq3322 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3322
  have eq4850 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4798 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4798
    | (have j0 := eq4798 X0 X1
       grind)
    | exact resolve eq4798 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4798
  have eq18794 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3242 x y
       grind)
    | exact superpose eq3242 eq16
    | (have j1 := eq3242 x y
       grind)
    | exact resolve eq16 eq3242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3242
  have eq20076 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18794
       have i₂ := eq4850 y x
       grind)
    | exact superpose eq4850 eq18794
    | (have j1 := eq4850 (σ y) (σ x)
       grind)
    | (have r₁ := eq18794
       have r₂ := eq4850 y x
       grind)
    | exact resolve eq18794 eq4850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4850 eq18794
  have eq20079 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20076
  have eq20584 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (M.op x (M.op y x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq20079
       grind)
    | exact superpose eq20079 eq9
    | exact resolve eq9 eq20079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20079
  have eq20662 : ∀ X0 X1 : G, (M.op X1 (M.op x (M.op y x))) = X1 ∨ (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (σ x) (σ y)
       have i₂ := eq20584 X1
       grind)
    | exact superpose eq20584 eq9
    | (have j1 := eq20584 X1
       grind)
    | exact resolve eq9 eq20584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20584
  have eq362771 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ x) (M.op (σ y) (σ x)))) = X2 ∨ (M.op X0 (M.op X1 (M.op y X1))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 X0 y x
       have i₂ := eq20662 X2 y
       grind)
    | exact superpose eq20662 eq19
    | (have j1 := eq20662 X2 X1
       grind)
    | exact resolve eq19 eq20662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20662
  have eq395075 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op (τ (σ y)) X1))) = X0 ∨ (M.op X2 (M.op X3 (M.op y X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq621 X1 X0 (σ y) (σ x)
       have i₂ := eq362771 X2 X3 (σ y)
       grind)
    | exact superpose eq362771 eq621
    | (have j1 := eq362771 X2 X3 X2
       grind)
    | exact resolve eq621 eq362771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621 eq362771
  have eq396617 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op y X1))) = X0 ∨ (M.op X2 (M.op X3 (M.op y X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq395075 X0 X1 X2 X3
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq395075
    | (have j0 := eq395075 X0 X1 X0 X1
       grind)
    | exact resolve eq395075 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395075
  have eq429779 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 (M.op X1 (M.op y X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq396617 X0 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396617
  have eq429780 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op y X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq429779 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429779
  have eq429992 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq429780 y x
       grind)
    | exact superpose eq429780 eq9
    | exact resolve eq9 eq429780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430026 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq482 y x X0
       have i₂ := eq429780 y x
       grind)
    | exact superpose eq429780 eq482
    | exact resolve eq482 eq429780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482 eq429780
  have eq442183 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq430026 (σ x)
       grind)
    | exact superpose eq430026 eq16
    | exact resolve eq16 eq430026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430026
  have eq442591 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq442183
       have i₂ := eq429992 x
       grind)
    | exact superpose eq429992 eq442183
    | exact resolve eq442183 eq429992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429992 eq442183
  have eq442592 : False := by grind
  exact eq442592

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_x_pyy_pxy_Equation452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq63 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X1))) ≠ (M.op X0 (M.op X1 (M.op X0 X1))) ∨ (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 (M.op X1 (M.op X0 X1)))
       have i₂ := eq9 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op X2 (M.op X1 X2)))
       have r₂ := eq9 (M.op X1 (M.op X2 (M.op X1 X2))) X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq63 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq67 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X2 (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X0 (M.op X1 (M.op X2 (M.op X1 X2)))
       have i₂ := eq64 X1 X2 (σ X0)
       grind)
    | exact superpose eq64 eq28
    | exact resolve eq28 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq70 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X2 (M.op X1 X2))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq67
    | exact resolve eq67 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq795 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq1401 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq795 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq795
    | (have j0 := eq795 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq795 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1425 : ∀ X0 X1 : G, (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq795 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq795
    | (have j0 := eq795 (σ X0) (σ X1)
       grind)
    | exact resolve eq795 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq9567 : ∀ X0 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq1425 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425
  have eq9568 : ∀ X0 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
    intro X0
    first
    | (have j0 := eq9567 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9567
  have eq10625 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1401 x y
       grind)
    | exact superpose eq1401 eq16
    | (have j1 := eq1401 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1401 x y
       grind)
    | exact resolve eq16 eq1401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401
  have eq10699 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq10625
  have eq10991 : ∀ X0 : G, (σ (σ (τ X0))) ≠ (σ (k (σ (τ X0)) X0)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq9568 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq9568
    | (have j0 := eq9568 (τ X0)
       grind)
    | exact resolve eq9568 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9568
  have eq11051 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq10991 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10991
    | (have j0 := eq10991 X0
       grind)
    | exact resolve eq10991 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10991
  have eq11080 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11051 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11051
    | (have j0 := eq11051 X0
       grind)
    | exact resolve eq11051 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11051
  have eq11155 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11080 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq11080
    | (have j0 := eq11080 (τ X0)
       grind)
    | exact resolve eq11080 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq11215 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11155 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11155
    | (have j0 := eq11155 X0
       grind)
    | exact resolve eq11155 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11155
  have eq11244 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11215 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11215
    | (have j0 := eq11215 X0
       grind)
    | exact resolve eq11215 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11215
  have eq11298 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq11244 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq11244
    | (have j0 := eq11244 (τ X0)
       grind)
    | exact resolve eq11244 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq25236 : ∀ X0 : G, (k X0 (τ (M.op (σ y) (M.op (σ y) (σ y))))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq70 X0 (σ y) (σ y)
       have i₂ := eq10699
       grind)
    | exact superpose eq10699 eq70
    | exact resolve eq70 eq10699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq25363 : ∀ X0 : G, (k X0 (τ (M.op (σ y) (σ y)))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq10699 eq25236
    | exact resolve eq25236 eq10699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25236
  have eq25431 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq10699 eq25363
    | exact resolve eq25363 eq10699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10699 eq25363
  have eq25450 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq25431 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq25431
    | exact resolve eq25431 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25431
  have eq25452 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq25450 X0
       have j1 := eq12 X0 y
       grind)
    | (have r₁ := eq25450 X0
       have r₂ := eq12 X0 y
       grind)
    | exact resolve eq25450 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25450
  have eq25455 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (k X1 y) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (σ x) (σ y)
       have i₂ := eq25452 X1
       grind)
    | exact superpose eq25452 eq9
    | (have j1 := eq25452 X1
       grind)
    | exact resolve eq9 eq25452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25452
  have eq25530 : ∀ X0 X1 : G, (k X0 (σ y)) = X0 ∨ (k X1 y) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (σ y) (σ x) X0
       have i₂ := eq25455 (σ y) X1
       grind)
    | exact superpose eq25455 eq64
    | (have j1 := eq25455 X0 X1
       grind)
    | exact resolve eq64 eq25455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25455
  have eq26199 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (k X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11298 (σ y)
       have i₂ := eq25530 (σ y) X0
       grind)
    | exact superpose eq25530 eq11298
    | (have j0 := eq11298 (σ y)
       have j1 := eq25530 X0 X0
       grind)
    | exact resolve eq11298 eq25530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11298 eq25530
  have eq26266 : ∀ X0 : G, (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (k X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq26199 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26199
  have eq26339 : ∀ X0 : G, y = (M.op y y) ∨ (k X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26266 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq26266
    | (have j0 := eq26266 X0
       grind)
    | exact resolve eq26266 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26266
  have eq26398 : ∀ X0 : G, x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq26339 X0
       have j1 := eq12 X0 y
       grind)
    | (have r₁ := eq26339 X0
       have r₂ := eq12 X0 y
       grind)
    | exact resolve eq26339 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26339
  have eq26415 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op y x))) = X0 ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq26398 X1
       grind)
    | exact superpose eq26398 eq9
    | (have j1 := eq26398 X1
       grind)
    | exact resolve eq9 eq26398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26398
  have eq26492 : ∀ X0 X1 : G, (k X1 y) = X1 ∨ (k X0 y) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq64 y x X1
       have i₂ := eq26415 y X0
       grind)
    | exact superpose eq26415 eq64
    | (have j1 := eq26415 X0 X1
       grind)
    | exact resolve eq64 eq26415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq26415
  have eq27062 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq26492 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26492
  have eq27063 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq27062 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27062
  have eq27145 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq27063 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27063
  have eq27238 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq11080 y
       have i₂ := eq27145 y
       grind)
    | exact superpose eq27145 eq11080
    | (have j0 := eq11080 y
       grind)
    | exact resolve eq11080 eq27145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11080
  have eq27239 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11244 y
       have i₂ := eq27145 y
       grind)
    | exact superpose eq27145 eq11244
    | (have j0 := eq11244 y
       grind)
    | (have r₁ := eq11244 y
       have r₂ := eq27145 y
       grind)
    | exact resolve eq11244 eq27145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11244 eq27145
  have eq27294 : y = (M.op y y) := by grind
  clear eq27239
  have eq27295 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq27238
  have eq27390 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq27294
       grind)
    | exact superpose eq27294 eq9
    | exact resolve eq9 eq27294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27526 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq27390 X0
       have i₂ := eq27294
       grind)
    | exact superpose eq27294 eq27390
    | exact resolve eq27390 eq27294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27390
  have eq27594 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq27526 X0
       have i₂ := eq27294
       grind)
    | exact superpose eq27294 eq27526
    | exact resolve eq27526 eq27294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27294 eq27526
  have eq27837 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27594 x
       grind)
    | exact superpose eq27594 eq16
    | exact resolve eq16 eq27594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27594
  have eq29526 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ y)
       have i₂ := eq27295
       grind)
    | exact superpose eq27295 eq9
    | exact resolve eq9 eq27295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29663 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq29526 X0
       have i₂ := eq27295
       grind)
    | exact superpose eq27295 eq29526
    | exact resolve eq29526 eq27295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29526
  have eq29732 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq29663 X0
       have i₂ := eq27295
       grind)
    | exact superpose eq27295 eq29663
    | exact resolve eq29663 eq27295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27295 eq29663
  have eq29746 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq27837
       have i₂ := eq29732 (σ x)
       grind)
    | exact superpose eq29732 eq27837
    | (have r₁ := eq27837
       have r₂ := eq29732 (σ x)
       grind)
    | exact resolve eq27837 eq29732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27837 eq29732
  have eq29884 : False := by grind
  exact eq29884

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | (have j0 := eq60 X0
       grind)
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq82 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = X0 := by
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
  have eq84 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq25
    | (have j1 := eq14 (σ X0) (M.op (σ X0) (σ X0))
       grind)
    | exact resolve eq25 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq146 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq57 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq57 X0
       grind)
    | exact resolve eq12 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq57 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq148 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq146 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq146 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq146 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq221 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq147 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq147
    | (have j0 := eq147 (τ X0)
       grind)
    | exact resolve eq147 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq222 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq221 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq221
    | (have j0 := eq221 X0
       grind)
    | exact resolve eq221 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq227 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq222 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq222
    | (have j0 := eq222 X0
       grind)
    | exact resolve eq222 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq234 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq227 (τ X0)
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq227
    | (have j0 := eq227 (τ X0)
       grind)
    | exact resolve eq227 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq378 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq63 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq63
    | exact resolve eq63 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq403 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq378 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq378
    | (have j0 := eq378 X0
       grind)
    | exact resolve eq378 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq404 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (σ (k X0 X0))) = (σ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq403 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq403
    | (have j0 := eq403 (σ X0)
       grind)
    | exact resolve eq403 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq502 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq82
    | (have j0 := eq82 X1 X1
       grind)
    | exact resolve eq82 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq536 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq502 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq502
    | (have j0 := eq502 X0 X1
       grind)
    | exact resolve eq502 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq7122 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ (σ (k X0 X0))) = (σ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq404 X0
       grind)
    | exact superpose eq404 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq404 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq404 X0
       grind)
    | exact resolve eq12 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq7134 : ∀ X0 X1 : G, (σ (σ (k X0 X0))) = (σ (M.op (σ X0) (σ X0))) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq7122 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7122
  have eq85396 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (σ (k (τ X0) (τ X0)))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq7134 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7134
    | exact resolve eq7134 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7134
  have eq85724 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k (σ (τ X0)) X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq85396 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq85396
    | (have j0 := eq85396 X0 X1
       grind)
    | exact resolve eq85396 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq85396
  have eq85758 : ∀ X0 X1 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq85724 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq85724
    | (have j0 := eq85724 X0 X1
       grind)
    | exact resolve eq85724 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85724
  have eq86451 : ∀ X0 X1 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq85758 X0 X1
       grind)
    | exact superpose eq85758 eq10
    | (have j1 := eq85758 X0 X1
       grind)
    | exact resolve eq10 eq85758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85758
  have eq86598 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq86451 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq86451
    | (have j0 := eq86451 X0 X0
       grind)
    | exact resolve eq86451 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86451
  have eq87052 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq86598 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86598
  have eq87053 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq87052 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87052
  have eq87780 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 X1
       have i₂ := eq87053 X0
       grind)
    | exact superpose eq87053 eq148
    | (have j0 := eq148 X0 X1
       grind)
    | exact resolve eq148 eq87053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq87783 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq234 X0
       have i₂ := eq87053 X0
       grind)
    | exact superpose eq87053 eq234
    | (have j0 := eq234 X0
       grind)
    | exact resolve eq234 eq87053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq87897 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq87053 (σ X0)
       grind)
    | exact superpose eq87053 eq15
    | exact resolve eq15 eq87053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87914 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0 X0
       have i₂ := eq87053 (τ X0)
       grind)
    | exact superpose eq87053 eq36
    | exact resolve eq36 eq87053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq88010 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq87914 X0
       have i₂ := eq87053 X0
       grind)
    | exact superpose eq87053 eq87914
    | exact resolve eq87914 eq87053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87914
  have eq88025 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq87897 X0
       have i₂ := eq87053 X0
       grind)
    | exact superpose eq87053 eq87897
    | exact resolve eq87897 eq87053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87053 eq87897
  have eq96462 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq87783 (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq87783
    | (have j0 := eq87783 (σ X0)
       have j1 := eq84 X0 X1
       grind)
    | exact resolve eq87783 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq87783
  have eq96659 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq96462 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96462
  have eq96800 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq96659 X0 X1
       have i₂ := eq88010 (σ X0)
       grind)
    | exact superpose eq88010 eq96659
    | (have j0 := eq96659 X0 X1
       grind)
    | exact resolve eq96659 eq88010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88010 eq96659
  have eq96923 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq96800 X0 X1
       have i₂ := eq88025 X0
       grind)
    | exact superpose eq88025 eq96800
    | (have j0 := eq96800 X0 X1
       grind)
    | exact resolve eq96800 eq88025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96800
  have eq97023 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ X0) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq96923 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq96923
    | (have j0 := eq96923 X0 X1
       grind)
    | exact resolve eq96923 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96923
  have eq97082 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq97023 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq97023
    | (have j0 := eq97023 X0 X1
       grind)
    | exact resolve eq97023 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97023
  have eq214615 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) X0)
       have i₂ := eq97082 X1 X0
       grind)
    | exact superpose eq97082 eq11
    | (have j1 := eq97082 X1 X0
       grind)
    | exact resolve eq11 eq97082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97082
  have eq214847 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq214615 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq214615
    | (have j0 := eq214615 X0 X1
       grind)
    | exact resolve eq214615 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq214615
  have eq215385 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq214847 (σ X1) X0
       grind)
    | exact superpose eq214847 eq15
    | (have j1 := eq214847 (σ X1) X0
       grind)
    | exact resolve eq15 eq214847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214847
  have eq404245 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq215385 x y
       grind)
    | exact superpose eq215385 eq16
    | (have j1 := eq215385 x y
       grind)
    | exact resolve eq16 eq215385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215385
  have eq406181 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq404245
       have i₂ := eq536 y x
       grind)
    | exact superpose eq536 eq404245
    | (have j1 := eq536 (σ x) (σ y)
       grind)
    | (have r₁ := eq404245
       have r₂ := eq536 y x
       grind)
    | (have r₁ := eq404245
       have r₂ := eq536 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq404245
       have r₂ := eq536 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq404245 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536 eq404245
  have eq406182 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq406181
  have eq406183 : x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq406182
  have eq406190 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq406183
       grind)
    | exact superpose eq406183 eq16
    | exact resolve eq16 eq406183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406183
  have eq406193 : (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq406190
       have r₂ := eq88025 x
       grind)
    | exact resolve eq406190 eq88025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406190
  have eq406495 : y = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq406193
       grind)
    | exact superpose eq406193 eq10
    | exact resolve eq10 eq406193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406193
  have eq406826 : x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq406495
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq406495
    | exact resolve eq406495 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406495
  have eq406909 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq406826
       grind)
    | exact superpose eq406826 eq16
    | exact resolve eq16 eq406826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406826
  have eq406912 : x = (M.op x x) := by
    first
    | (have r₁ := eq406909
       have r₂ := eq88025 x
       grind)
    | exact resolve eq406909 eq88025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88025 eq406909
  have eq407712 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq406912
       grind)
    | exact superpose eq406912 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq406912
       grind)
    | exact resolve eq12 eq406912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407721 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq87780 x X0
       have i₂ := eq406912
       grind)
    | exact superpose eq406912 eq87780
    | (have j0 := eq87780 x X0
       grind)
    | exact resolve eq87780 eq406912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87780 eq406912
  have eq407917 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq407721 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407721
  have eq407919 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq407712 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407712
  have eq425599 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq407917 (σ X0)
       grind)
    | exact superpose eq407917 eq15
    | exact resolve eq15 eq407917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407917
  have eq425770 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq425599 X0
       have i₂ := eq407919 X0
       grind)
    | exact superpose eq407919 eq425599
    | exact resolve eq425599 eq407919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407919 eq425599
  have eq471826 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq425770 y
       grind)
    | exact superpose eq425770 eq16
    | (have r₁ := eq16
       have r₂ := eq425770 y
       grind)
    | exact resolve eq16 eq425770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425770
  have eq472267 : False := by grind
  exact eq472267
