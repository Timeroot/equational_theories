import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pxy_Equation3532 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  clear eq18
  have eq103 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq103 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq103
    | exact resolve eq103 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq169 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq171 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq556 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq169 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq169
    | (have j0 := eq169 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq169 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39277 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq556 x y
       grind)
    | exact superpose eq556 eq16
    | (have j1 := eq556 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq556 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq556 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq556 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq39341 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq39277
  have eq39439 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq39341
       grind)
    | exact superpose eq39341 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq39341
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq39341
       grind)
    | exact resolve eq13 eq39341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39341
  have eq39461 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq39439
  have eq39462 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq39461
  have eq39478 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq39462
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq39462
    | exact resolve eq39462 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39462
  have eq39488 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq14 eq39478
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq39478 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39478
  have eq39491 : (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq39488
       grind)
    | exact superpose eq39488 eq10
    | exact resolve eq10 eq39488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39488
  have eq39648 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq39491
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq39491
    | exact resolve eq39491 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39491
  have eq39650 : y ≠ y ∨ x = y ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq39648
       grind)
    | exact superpose eq39648 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq39648
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq39648
       grind)
    | exact resolve eq13 eq39648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39651 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq105 X1 x X0 y
       have i₂ := eq39648
       grind)
    | exact superpose eq39648 eq105
    | exact resolve eq105 eq39648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39672 : y ≠ y ∨ x = y ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq39650
  have eq39673 : x = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq39672
  have eq39675 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq169 x y
       have i₂ := eq39673
       grind)
    | exact superpose eq39673 eq169
    | (have j0 := eq169 y x
       grind)
    | exact resolve eq169 eq39673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39673
  have eq39678 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq39675
  have eq39680 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq39651 X0 x
       have i₂ := eq39648
       grind)
    | exact superpose eq39648 eq39651
    | exact resolve eq39651 eq39648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39648 eq39651
  have eq39931 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq39680 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39680
  have eq522217 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq171 (σ y) x
       have i₂ := eq39678
       grind)
    | exact superpose eq39678 eq171
    | (have j0 := eq171 (σ y) x
       grind)
    | exact resolve eq171 eq39678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq39678
  have eq522273 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq522217
  have eq522311 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq522273
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq522273
    | exact resolve eq522273 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522273
  have eq522342 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq522311
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq522311
       have r₂ := eq13 y x
       grind)
    | exact resolve eq522311 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522311
  have eq522482 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq522342
       grind)
    | exact superpose eq522342 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq522342
       grind)
    | exact resolve eq13 eq522342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522342
  have eq522535 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ x = y := by grind
  clear eq522482
  have eq522536 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ x = y := by grind
  clear eq522535
  have eq522575 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq522536
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq522536
    | exact resolve eq522536 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522536
  have eq522603 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq522575
       grind)
    | exact superpose eq522575 eq10
    | exact resolve eq10 eq522575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522575
  have eq522824 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq522603
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq522603
    | exact resolve eq522603 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522603
  have eq522825 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq522824
  have eq522828 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq169 y x
       have i₂ := eq522825
       grind)
    | exact superpose eq522825 eq169
    | (have j0 := eq169 x y
       grind)
    | exact resolve eq169 eq522825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169 eq522825
  have eq522841 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq522828
  have eq523006 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq105 X1 (σ x) X0 (σ y)
       have i₂ := eq522841
       grind)
    | exact superpose eq522841 eq105
    | exact resolve eq105 eq522841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq528594 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq523006 X0 (σ x)
       have i₂ := eq522841
       grind)
    | exact superpose eq522841 eq523006
    | exact resolve eq523006 eq522841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522841 eq523006
  have eq529501 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq528594 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528594
  have eq530799 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq529501 (σ x)
       grind)
    | exact superpose eq529501 eq16
    | exact resolve eq16 eq529501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530946 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq529501
  have eq530962 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq530946
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq530946
    | exact resolve eq530946 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530946
  have eq530996 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq530799
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq530799
    | exact resolve eq530799 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530799
  have eq546437 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq530996
       have i₂ := eq39931 x
       grind)
    | exact superpose eq39931 eq530996
    | exact resolve eq530996 eq39931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530996
  have eq546438 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq546437
  have eq546439 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq546438
  have eq546460 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X1 (σ y) X0 (σ x)
       have i₂ := eq546439
       grind)
    | exact superpose eq546439 eq105
    | exact resolve eq105 eq546439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546587 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq546460 X0 (σ y)
       have i₂ := eq546439
       grind)
    | exact superpose eq546439 eq546460
    | exact resolve eq546460 eq546439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546439 eq546460
  have eq547516 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq546587 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546587
  have eq548793 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq547516 (σ x)
       grind)
    | exact superpose eq547516 eq16
    | exact resolve eq16 eq547516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547516
  have eq548998 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq548793
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq548793
    | exact resolve eq548793 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548793
  have eq549376 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq39931 eq548998
    | exact resolve eq548998 eq39931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39931 eq548998
  have eq549377 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq549376
  have eq550335 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op x X1)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X1 y X0 x
       have i₂ := eq549377
       grind)
    | exact superpose eq549377 eq105
    | exact resolve eq105 eq549377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq555422 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq550335 X0 y
       have i₂ := eq549377
       grind)
    | exact superpose eq549377 eq550335
    | exact resolve eq550335 eq549377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550335
  have eq556306 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq555422 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555422
  have eq557514 : x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq549377
       have i₂ := eq556306 x
       grind)
    | exact superpose eq556306 eq549377
    | exact resolve eq549377 eq556306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556306
  have eq557517 : x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq557514
  have eq558124 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq557517 eq530962
    | exact resolve eq530962 eq557517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530962 eq557517
  have eq558323 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq558124
  have eq558713 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq558323
       grind)
    | exact superpose eq558323 eq16
    | exact resolve eq16 eq558323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558323
  have eq558826 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq549377 eq558713
    | exact resolve eq558713 eq549377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549377 eq558713
  have eq558827 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq558826
  have eq558940 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq558827
       grind)
    | exact superpose eq558827 eq10
    | exact resolve eq10 eq558827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558827
  have eq559156 : x = y ∨ x = y := by
    first
    | (have i₁ := eq558940
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq558940
    | exact resolve eq558940 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558940
  have eq559157 : x = y := by grind
  clear eq559156
  have eq559160 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq559157
       grind)
    | exact superpose eq559157 eq16
    | exact resolve eq16 eq559157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559157
  have eq559161 : False := by grind
  exact eq559161

/-- `Equation3555`: `x ◇ y = y ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pyx_y_pyx_Equation3555 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3555 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3555.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X1 X0) X0)) := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq21 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
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
  have eq262 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X0
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
  have eq263 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq262 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq262
    | (have j0 := eq262 (σ X0) X1
       grind)
    | exact resolve eq262 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq262 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq262
    | (have j0 := eq262 (τ X0) X1
       grind)
    | exact resolve eq262 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq287 : ∀ X0 X1 X2 : G, (k (k X1 (σ X2)) (σ X0)) = (σ (M.op X0 (k (τ X1) X2))) ∨ (k (τ X1) X2) = (M.op (k (τ X1) X2) (k (τ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X1 X2 X0
       have i₂ := eq262 (k (τ X1) X2) X0
       grind)
    | exact superpose eq262 eq21
    | (have j1 := eq262 (k (τ X1) X2) X1
       grind)
    | exact resolve eq21 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq337 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq263 X1 X0
       have i₂ := eq262 X1 X0
       grind)
    | exact superpose eq262 eq263
    | (have j0 := eq263 X1 X1
       have j1 := eq262 (σ X1) X1
       grind)
    | exact resolve eq263 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq529 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k (τ X0) X1) = X1 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq264 X0 X0
       grind)
    | exact superpose eq264 eq13
    | (have j0 := eq13 (τ X0) X1
       have j1 := eq264 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq264 X0 X1
       grind)
    | exact resolve eq13 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq264 X0 X0
       grind)
    | exact superpose eq264 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq264 X0 X1
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq264 X0 X1
       grind)
    | exact resolve eq12 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq264 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq539 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq530 X0 X1
       have j1 := eq12 X1 (τ X0)
       grind)
    | (have r₁ := eq530 X0 X1
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq530 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq540 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq529 X0 X1
       have j1 := eq13 (τ X0) X1
       grind)
    | (have r₁ := eq529 X0 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq529 X0 X1
       have r₂ := eq13 (τ X0) X1
       grind)
    | exact resolve eq529 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq591 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq539 (σ X0) X1
       have i₂ := eq28 X0 (σ X0)
       grind)
    | exact superpose eq28 eq539
    | (have j0 := eq539 (σ X0) X1
       grind)
    | exact resolve eq539 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq592 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq591 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq591
    | (have j0 := eq591 X0 X1
       grind)
    | exact resolve eq591 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq595 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq592 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq592
    | (have j0 := eq592 X0 X1
       grind)
    | exact resolve eq592 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq600 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq595 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq595
    | (have j0 := eq595 (σ X0) X1
       grind)
    | exact resolve eq595 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq631 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (M.op X1 X1) = X1 ∨ (k (τ (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq540 (σ X0) X1
       have i₂ := eq28 X0 (σ X0)
       grind)
    | exact superpose eq28 eq540
    | (have j0 := eq540 (σ X0) X1
       grind)
    | exact resolve eq540 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq632 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k (τ (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq631 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq631
    | (have j0 := eq631 X0 X1
       grind)
    | exact resolve eq631 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq635 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq632 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq632
    | (have j0 := eq632 X0 X1
       grind)
    | exact resolve eq632 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq640 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq635 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq635
    | (have j0 := eq635 (σ X0) X1
       grind)
    | exact resolve eq635 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq1945 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq337 x y
       grind)
    | exact superpose eq337 eq16
    | (have j1 := eq337 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq337 x y
       grind)
    | exact resolve eq16 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1958 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1945
  have eq1970 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ y)
       have i₂ := eq1958
       grind)
    | exact superpose eq1958 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq1958
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq1958
       grind)
    | exact resolve eq12 eq1958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1974 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq1970 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1970
  have eq1996 : (τ (M.op (σ y) (σ y))) ≠ (τ (σ y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq534 (σ y)
       have i₂ := eq1974 (σ y)
       grind)
    | exact superpose eq1974 eq534
    | (have j0 := eq534 (σ y)
       grind)
    | exact resolve eq534 eq1974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534 eq1974
  have eq2052 : y ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1996
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1996
    | exact resolve eq1996 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1996
  have eq2055 : y = (M.op y y) ∨ y ≠ (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2052
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2052
    | exact resolve eq2052 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052
  have eq2056 : y = (M.op y y) ∨ y ≠ (τ (M.op (σ y) (σ y))) := by grind
  clear eq2055
  have eq2059 : y = (M.op y y) ∨ y ≠ (τ (σ y)) := by
    first
    | exact superpose eq1958 eq2056
    | exact resolve eq2056 eq1958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958 eq2056
  have eq2060 : y = (M.op y y) := by
    first
    | (have r₁ := eq2059
       have r₂ := eq10 y
       grind)
    | exact resolve eq2059 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059
  have eq2062 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq2060
       grind)
    | exact superpose eq2060 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq2060
       grind)
    | exact resolve eq12 eq2060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2066 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq2062 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2062
  have eq2075 : ∀ X0 : G, (τ y) ≠ (τ (M.op y y)) ∨ (M.op X0 X0) = X0 ∨ (k (τ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq540 y X0
       have i₂ := eq2066 y
       grind)
    | exact superpose eq2066 eq540
    | (have j0 := eq540 y X0
       grind)
    | exact resolve eq540 eq2066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq2079 : ∀ X0 : G, (σ y) ≠ (σ (M.op y y)) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq600 y X0
       have i₂ := eq2066 y
       grind)
    | exact superpose eq2066 eq600
    | (have j0 := eq600 y X0
       grind)
    | exact resolve eq600 eq2066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq2081 : ∀ X0 : G, (σ y) ≠ (σ (M.op y y)) ∨ (k (σ y) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq640 y X0
       have i₂ := eq2066 y
       grind)
    | exact superpose eq2066 eq640
    | (have j0 := eq640 y X0
       grind)
    | exact resolve eq640 eq2066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq2100 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2081 X0
       have i₂ := eq2060
       grind)
    | exact superpose eq2060 eq2081
    | (have j0 := eq2081 X0
       grind)
    | exact resolve eq2081 eq2060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2081
  have eq2101 : ∀ X0 : G, (k (σ y) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2100 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2100
  have eq2102 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2079 X0
       have i₂ := eq2060
       grind)
    | exact superpose eq2060 eq2079
    | (have j0 := eq2079 X0
       grind)
    | exact resolve eq2079 eq2060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2079
  have eq2103 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq2102 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2102
  have eq2106 : ∀ X0 : G, (τ y) ≠ (τ y) ∨ (M.op X0 X0) = X0 ∨ (k (τ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2075 X0
       have i₂ := eq2060
       grind)
    | exact superpose eq2060 eq2075
    | (have j0 := eq2075 X0
       grind)
    | exact resolve eq2075 eq2060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2060 eq2075
  have eq2107 : ∀ X0 : G, (k (τ y) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2106 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2106
  have eq2163 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq2103 (σ X0)
       grind)
    | exact superpose eq2103 eq15
    | exact resolve eq15 eq2103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2103
  have eq2211 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq2163 X0
       have i₂ := eq2066 X0
       grind)
    | exact superpose eq2066 eq2163
    | exact resolve eq2163 eq2066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2066 eq2163
  have eq2529 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (M.op (σ y) (M.op (σ (M.op y X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ y)
       have i₂ := eq2211 X0
       grind)
    | exact superpose eq2211 eq9
    | exact resolve eq9 eq2211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2879 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ y)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq22 (σ y) X0
       have i₂ := eq2101 (σ X0)
       grind)
    | exact superpose eq2101 eq22
    | (have j1 := eq2101 (σ X0)
       grind)
    | exact resolve eq22 eq2101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2101
  have eq2933 : ∀ X0 : G, (τ (σ X0)) = (k y X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2879 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2879
    | (have j0 := eq2879 X0
       grind)
    | exact resolve eq2879 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2879
  have eq2964 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2933 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2933
    | (have j0 := eq2933 X0
       grind)
    | exact resolve eq2933 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2933
  have eq3016 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ y)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ y)
       have i₂ := eq2107 (τ X0)
       grind)
    | exact superpose eq2107 eq18
    | (have j1 := eq2107 (τ X0)
       grind)
    | exact resolve eq18 eq2107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2107
  have eq3042 : ∀ X0 : G, (σ (τ X0)) = (k y X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq3016 X0
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq3016
    | (have j0 := eq3016 X0
       grind)
    | exact resolve eq3016 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3016
  have eq3076 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3042 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3042
    | (have j0 := eq3042 X0
       grind)
    | exact resolve eq3042 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3042
  have eq4096 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (k y X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq2964 X0
       grind)
    | exact superpose eq2964 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq2964 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq2964 X0
       grind)
    | exact resolve eq12 eq2964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4102 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (k y X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq4096 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4096
  have eq4143 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k y X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq3076 X0
       grind)
    | exact superpose eq3076 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq3076 X0
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq3076 X0
       grind)
    | exact resolve eq12 eq3076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3076
  have eq4149 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k y X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq4143 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4143
  have eq4837 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4102 X1 (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4102
    | (have j0 := eq4102 X1 X1
       grind)
    | exact resolve eq4102 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4859 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (M.op (σ X0) (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (k y X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq539 (σ X0) X1
       have i₂ := eq4102 X0 (σ X0)
       grind)
    | exact superpose eq4102 eq539
    | (have j0 := eq539 (σ X0) X1
       have j1 := eq4102 X0 X1
       grind)
    | exact resolve eq539 eq4102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4102
  have eq4921 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (k y X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4859 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4859
    | (have j0 := eq4859 X0 X1
       grind)
    | exact resolve eq4859 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4859
  have eq4924 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (τ (M.op (σ X0) (σ X0))) ≠ X0 ∨ (k y X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4921 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4921
    | (have j0 := eq4921 X0 X1
       grind)
    | exact resolve eq4921 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4921
  have eq4927 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (τ (σ X0)) ≠ X0 ∨ (k y X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq2964 eq4924
    | (have j0 := eq4924 X0 X1
       have j1 := eq2964 X0
       grind)
    | exact resolve eq4924 eq2964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2964 eq4924
  have eq4929 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k y X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq4927 X0 X1
       grind)
    | (have r₁ := eq4927 X0 X1
       have r₂ := eq10 X0
       grind)
    | exact resolve eq4927 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4927
  have eq5054 : ∀ X0 X1 : G, (σ X0) = (k y (σ X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4149 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4149
    | (have j0 := eq4149 (σ X0) X1
       grind)
    | exact resolve eq4149 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4149
  have eq5502 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ y) X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 y X0
       have i₂ := eq5054 X0 X1
       grind)
    | exact superpose eq5054 eq22
    | (have j1 := eq5054 X0 X1
       grind)
    | exact resolve eq22 eq5054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq5527 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k (τ y) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5502 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5502
    | (have j0 := eq5502 X0 X1
       grind)
    | exact resolve eq5502 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5502
  have eq9070 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k y X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq4929 eq4837
    | (have j0 := eq4837 X0 X1
       have j1 := eq4929 X1 X1
       grind)
    | exact resolve eq4837 eq4929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4837 eq4929
  have eq9490 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9070 y x
       grind)
    | exact superpose eq9070 eq16
    | (have j1 := eq9070 x x
       grind)
    | (have r₁ := eq16
       have r₂ := eq9070 y x
       grind)
    | exact resolve eq16 eq9070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9070
  have eq9510 : x = (k y x) := by grind
  clear eq9490
  have eq81152 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 (k (τ y) X0))) ∨ (k (τ y) X0) = (M.op (k (τ y) X0) (k (τ y) X0)) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq287 X1 y X0
       have i₂ := eq5054 X0 X2
       grind)
    | exact superpose eq5054 eq287
    | (have j0 := eq287 X0 y X0
       have j1 := eq5054 X0 X2
       grind)
    | exact resolve eq287 eq5054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287 eq5054
  have eq81404 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X1 (k (τ y) X0))) ∨ (k (τ y) X0) = (M.op (k (τ y) X0) (k (τ y) X0)) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81152 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq81152
    | (have j0 := eq81152 X0 X1 X2
       grind)
    | exact resolve eq81152 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81152
  have eq81545 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k (τ y) X0) = (M.op (k (τ y) X0) (k (τ y) X0)) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq5527 eq81404
    | (have j0 := eq81404 X0 X1 X2
       have j1 := eq5527 X0 X2
       grind)
    | exact resolve eq81404 eq5527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81404
  have eq81669 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X0 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq5527 eq81545
    | (have j0 := eq81545 X0 X1 X2
       have j1 := eq5527 X0 X2
       grind)
    | exact resolve eq81545 eq5527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5527 eq81545
  have eq81734 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq81669 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq81669 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq81669 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81669
  have eq81978 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81734 X0 (τ X1) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq81734
    | (have j0 := eq81734 X0 X1 X2
       grind)
    | exact resolve eq81734 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq82018 : ∀ X0 X1 X2 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X2 X1) = (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq81734 X1 X0 X2
       grind)
    | exact superpose eq81734 eq10
    | (have j1 := eq81734 X1 X1 X2
       grind)
    | exact resolve eq10 eq81734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81734
  have eq82358 : ∀ X0 X1 X2 : G, (k X2 X1) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq82018 X0 X1 X2
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq82018
    | (have j0 := eq82018 X0 X1 X2
       grind)
    | exact resolve eq82018 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82018
  have eq82531 : ∀ X0 X1 X2 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq539 X0 X1
       have i₂ := eq82358 X2 X0 X0
       grind)
    | exact superpose eq82358 eq539
    | (have j0 := eq539 X0 X1
       have j1 := eq82358 X0 (τ X0) X1
       grind)
    | exact resolve eq539 eq82358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq82807 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq82358 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82358
  have eq82808 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq82807 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82807
  have eq82827 : ∀ X0 X1 X2 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq262 eq82531
    | (have j0 := eq82531 X0 X1 X2
       have j1 := eq262 X1 (τ X0)
       grind)
    | exact resolve eq82531 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262 eq82531
  have eq82828 : ∀ X0 X1 X2 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq82827 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82827
  have eq82961 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq82808 (σ X0)
       grind)
    | exact superpose eq82808 eq15
    | exact resolve eq15 eq82808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83143 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq82961 X0
       have i₂ := eq82808 X0
       grind)
    | exact superpose eq82808 eq82961
    | exact resolve eq82961 eq82808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82808 eq82961
  have eq83642 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq337 X0 X1
       have i₂ := eq83143 X1
       grind)
    | exact superpose eq83143 eq337
    | (have j0 := eq337 X0 X1
       grind)
    | exact resolve eq337 eq83143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq94435 : ∀ X0 X1 X2 : G, (k (σ X0) X2) = (M.op X2 (σ X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq82828 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq82828
    | (have j0 := eq82828 (σ X0) X1 X2
       grind)
    | exact resolve eq82828 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82828
  have eq102198 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq94435 eq81978
    | (have j0 := eq81978 X0 X1 X2
       have j1 := eq94435 X0 X2 X2
       grind)
    | exact resolve eq81978 eq94435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81978 eq94435
  have eq102200 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X2 X1) = (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq102198 X1 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq102198
    | (have j0 := eq102198 X1 X1 X2
       grind)
    | exact resolve eq102198 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102198
  have eq103676 : ∀ X0 X1 : G, (M.op (σ X0) (σ y)) = (M.op (σ y) (σ (M.op (M.op y X0) X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2529 X0
       have i₂ := eq102200 (M.op y X0) X0 X1
       grind)
    | exact superpose eq102200 eq2529
    | (have j1 := eq102200 X0 X0 X1
       grind)
    | exact resolve eq2529 eq102200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102200
  have eq103765 : ∀ X0 X1 : G, (M.op (σ X0) (σ y)) = (σ (M.op y (M.op (M.op y X0) X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq103676 X0 X1
       have i₂ := eq2211 (M.op (M.op y X0) X0)
       grind)
    | exact superpose eq2211 eq103676
    | (have j0 := eq103676 X0 X1
       grind)
    | exact resolve eq103676 eq2211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103676
  have eq103775 : ∀ X0 X1 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq103765 X0 X1
       have i₂ := eq9 X0 y
       grind)
    | exact superpose eq9 eq103765
    | (have j0 := eq103765 X0 X1
       grind)
    | exact resolve eq103765 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103765
  have eq114260 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq103775 x X0
       grind)
    | exact superpose eq103775 eq16
    | (have j1 := eq103775 x X0
       grind)
    | (have r₁ := eq16
       have r₂ := eq103775 x x
       grind)
    | exact resolve eq16 eq103775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103775
  have eq114313 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq114260 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114260
  have eq114364 : x = (M.op x y) := by
    first
    | (have i₁ := eq9510
       have i₂ := eq114313 y
       grind)
    | exact superpose eq114313 eq9510
    | exact resolve eq9510 eq114313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9510 eq114313
  have eq114511 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq114364
       grind)
    | exact superpose eq114364 eq16
    | exact resolve eq16 eq114364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114513 : (M.op y x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq9 y x
       have i₂ := eq114364
       grind)
    | exact superpose eq114364 eq9
    | exact resolve eq9 eq114364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114530 : (M.op y x) = (M.op x x) := by
    first
    | (have i₁ := eq114513
       have i₂ := eq114364
       grind)
    | exact superpose eq114364 eq114513
    | exact resolve eq114513 eq114364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114513
  have eq114700 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ (M.op x x)) (σ x))) := by
    first
    | (have i₁ := eq2529 x
       have i₂ := eq114530
       grind)
    | exact superpose eq114530 eq2529
    | exact resolve eq2529 eq114530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114701 : (M.op x y) = (M.op y (M.op (M.op x x) x)) := by
    first
    | (have i₁ := eq9 x y
       have i₂ := eq114530
       grind)
    | exact superpose eq114530 eq9
    | exact resolve eq9 eq114530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114722 : x = (M.op y (M.op (M.op x x) x)) := by
    first
    | (have i₁ := eq114701
       have i₂ := eq114364
       grind)
    | exact superpose eq114364 eq114701
    | exact resolve eq114701 eq114364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114364 eq114701
  have eq126162 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op (M.op x x) x))) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq114700
       have i₂ := eq83642 (M.op x x) x
       grind)
    | exact superpose eq83642 eq114700
    | (have j1 := eq83642 x x
       grind)
    | exact resolve eq114700 eq83642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83642 eq114700
  have eq126203 : (M.op (σ x) (σ y)) = (σ (M.op y (M.op (M.op x x) x))) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq126162
       have i₂ := eq2211 (M.op (M.op x x) x)
       grind)
    | exact superpose eq2211 eq126162
    | exact resolve eq126162 eq2211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126162
  have eq126222 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq126203
       have i₂ := eq114722
       grind)
    | exact superpose eq114722 eq126203
    | exact resolve eq126203 eq114722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114722 eq126203
  have eq126232 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq126222
       have r₂ := eq114511
       grind)
    | exact resolve eq126222 eq114511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126222
  have eq126854 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq126232
       grind)
    | exact superpose eq126232 eq10
    | exact resolve eq10 eq126232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126232
  have eq127184 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq126854
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq126854
    | exact resolve eq126854 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126854
  have eq127185 : x = (M.op x x) := by grind
  clear eq127184
  have eq127381 : x = (M.op y x) := by
    first
    | (have i₁ := eq114530
       have i₂ := eq127185
       grind)
    | exact superpose eq127185 eq114530
    | exact resolve eq114530 eq127185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114530
  have eq127522 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq2529 x
       have i₂ := eq127381
       grind)
    | exact superpose eq127381 eq2529
    | exact resolve eq2529 eq127381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2529
  have eq127545 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x x))) := by
    first
    | (have i₁ := eq127522
       have i₂ := eq83143 x
       grind)
    | exact superpose eq83143 eq127522
    | exact resolve eq127522 eq83143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83143 eq127522
  have eq127560 : (M.op (σ x) (σ y)) = (σ (M.op y (M.op x x))) := by
    first
    | (have i₁ := eq127545
       have i₂ := eq2211 (M.op x x)
       grind)
    | exact superpose eq2211 eq127545
    | exact resolve eq127545 eq2211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2211 eq127545
  have eq127574 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq127560
       have i₂ := eq127185
       grind)
    | exact superpose eq127185 eq127560
    | exact resolve eq127560 eq127185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127185 eq127560
  have eq127586 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq127574
       have i₂ := eq127381
       grind)
    | exact superpose eq127381 eq127574
    | exact resolve eq127574 eq127381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127381 eq127574
  have eq127595 : False := by grind
  exact eq127595

/-- `Equation3583`: `x ◇ y = z ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_y_y_x_pxy_Equation3583 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3583 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3583.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k x y) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X0 X0) X1) X3
       have i₂ := eq14 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq57 X0 X1 x X3
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq97
    | exact resolve eq97 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq106 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq124 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq141 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq124 eq16
    | exact resolve eq16 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq148 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq125 eq16
    | exact resolve eq16 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq59 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq59
    | (have j0 := eq59 x y X0
       grind)
    | exact resolve eq59 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq59
    | (have j0 := eq59 (σ x) (σ y) X0
       grind)
    | exact resolve eq59 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X2 ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 X1)
       have i₂ := eq59 X0 X1 X2
       grind)
    | exact superpose eq59 eq13
    | (have j0 := eq13 X2 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 (M.op X0 X1) (M.op X0 X1)
       have r₂ := eq59 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op X0 (M.op x y)) = X0 ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq207 eq12
    | (have j0 := eq12 X0 (M.op x y)
       grind)
    | (have r₁ := eq12 X0 (M.op x y)
       have r₂ := eq207 (M.op x y)
       grind)
    | exact resolve eq12 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq207 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq207 (M.op x y)
       grind)
    | exact resolve eq13 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq220 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq227 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq207 eq225
    | (have j0 := eq225 X0
       grind)
    | exact resolve eq225 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq225
  have eq228 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op X0 (M.op (σ x) (σ y))) = X0 ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq208 eq12
    | (have j0 := eq12 X0 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 X0 (M.op (σ x) (σ y))
       have r₂ := eq208 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq12 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ X0 ∨ (M.op (σ x) (σ y)) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq208 eq13
    | (have j0 := eq13 X0 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (M.op (σ x) (σ y))
       have r₂ := eq208 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq13 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = X0 ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq228 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq235 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ (M.op (σ x) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq208 eq233
    | (have j0 := eq233 X0
       grind)
    | exact resolve eq233 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq233
  have eq236 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j0 := eq223 (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq253 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq261 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq236 eq125
    | exact resolve eq125 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq265 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq261
    | exact resolve eq261 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq268 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq265 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq269 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq268
  have eq274 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq269 eq59
    | exact resolve eq59 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq296 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq327 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have j0 := eq231 (M.op (σ x) (σ y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq499 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq81 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq580 : ∀ X0 : G, (k (τ X0) (k x y)) = (τ (k X0 (k (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq253 X0 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq253
    | exact resolve eq253 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq674 : ∀ X0 : G, (k (k x y) (τ X0)) = (τ (k (k (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq296 (k x y) X0
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq296
    | exact resolve eq296 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq684 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq20 eq296
    | (have j0 := eq296 (M.op x y) X0
       grind)
    | exact resolve eq296 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ x) (σ y)))) ∨ (σ X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq235 eq296
    | (have j1 := eq235 (σ X0)
       grind)
    | exact resolve eq296 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq296
  have eq704 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (σ y)))) = X0 ∨ (σ X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq693 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq693
    | (have j0 := eq693 X0
       grind)
    | exact resolve eq693 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq961 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq213 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq1043 : (M.op x y) = (τ (k (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq704 eq684
    | (have j1 := eq704 (M.op x y)
       grind)
    | exact resolve eq684 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684 eq704
  have eq1053 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (k (σ (M.op x y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq20 eq1043
    | exact resolve eq1043 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq1063 : (M.op x y) = (τ (k (σ (M.op x y)) (M.op (σ x) (σ y)))) := by
    first
    | (have r₁ := eq1053
       have r₂ := eq27
       grind)
    | exact resolve eq1053 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053
  have eq1070 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1063 eq15
    | exact resolve eq15 eq1063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1086 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20 eq1070
    | exact resolve eq1070 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070
  have eq22813 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22814 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq22813
    | exact resolve eq22813 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22813
  have eq22819 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq22814
       have r₂ := eq27
       grind)
    | exact resolve eq22814 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22814
  have eq22821 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq22819
    | exact resolve eq22819 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22819
  have eq26948 : (k (M.op x y) (k x y)) = (τ (k (k (σ (M.op x y)) (M.op (σ x) (σ y))) (k (σ x) (σ y)))) := by
    first
    | exact superpose eq1063 eq580
    | exact resolve eq580 eq1063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq27014 : (k (M.op x y) (k x y)) = (τ (k (σ (M.op x y)) (k (σ x) (σ y)))) := by
    first
    | exact superpose eq1086 eq26948
    | exact resolve eq26948 eq1086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26948
  have eq27061 : (k (M.op x y) (k x y)) = (τ (k (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27014
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq27014
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq27014 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27014
  have eq27096 : (k (M.op x y) (k x y)) = (τ (k (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq27061
    | exact resolve eq27061 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27061
  have eq27098 : (M.op x y) = (k (M.op x y) (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1063 eq27096
    | exact resolve eq27096 eq1063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27096
  have eq27100 : (M.op x y) = (k (M.op x y) (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq27098
    | exact resolve eq27098 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27098
  have eq28952 : (k (k x y) (M.op x y)) = (τ (k (k (σ x) (σ y)) (k (σ (M.op x y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq1063 eq674
    | exact resolve eq674 eq1063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq29049 : (k (k x y) (M.op x y)) = (τ (k (k (σ x) (σ y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq1086 eq28952
    | exact resolve eq28952 eq1086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086 eq28952
  have eq29096 : (τ (k (σ (M.op x y)) (σ (M.op x y)))) = (k (k x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq100 eq29049
    | exact resolve eq29049 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq29049
  have eq29155 : (k (M.op x y) (M.op x y)) = (k (k x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq148 eq29096
    | exact resolve eq29096 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq29096
  have eq29160 : (M.op x y) = (k (k x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq236 eq29155
    | exact resolve eq29155 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq29155
  have eq50121 : (M.op x y) = (k x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29160 eq227
    | (have j0 := eq227 (k x y)
       grind)
    | exact resolve eq227 eq29160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq29160
  have eq50126 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq50121
  have eq953392 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq22821 eq59
    | exact resolve eq59 eq22821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22821
  have eq953447 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq953392
    | (have j0 := eq953392 (σ x)
       grind)
    | exact resolve eq953392 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953392
  have eq953601 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq961 y y
       have i₂ := eq953447
       grind)
    | exact superpose eq953447 eq961
    | exact resolve eq961 eq953447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961 eq953447
  have eq959633 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq499 y y
       have i₂ := eq953601
       grind)
    | exact superpose eq953601 eq499
    | (have j0 := eq499 y y
       grind)
    | exact resolve eq499 eq953601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499 eq953601
  have eq959661 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq959633
  have eq959662 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq959661
  have eq959689 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq959662
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq959662
    | exact resolve eq959662 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959662
  have eq959824 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq959689 eq59
    | exact resolve eq59 eq959689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959689
  have eq960612 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq959824 eq26
    | (have j1 := eq959824 (σ x)
       grind)
    | exact resolve eq26 eq959824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959824
  have eq960613 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq960612
  have eq960641 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq960613 eq327
    | exact resolve eq327 eq960613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327 eq960613
  have eq965169 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq960641 eq106
    | exact resolve eq106 eq960641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq960641
  have eq965277 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq965169
    | exact resolve eq965169 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965169
  have eq965577 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq965277
       grind)
    | exact superpose eq965277 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq965277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965277
  have eq965610 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq965577
  have eq965731 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq59 y y x
       have i₂ := eq965610
       grind)
    | exact superpose eq965610 eq59
    | exact resolve eq59 eq965610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965610
  have eq965787 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq965731 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq965731
    | (have j0 := eq965731 x
       grind)
    | exact resolve eq965731 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965731
  have eq965934 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq965787 eq51
    | (have r₁ := eq51
       have r₂ := eq965787
       grind)
    | exact resolve eq51 eq965787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq965787
  have eq967526 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq965934
  have eq972012 : (τ (σ y)) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq967526 eq55
    | exact resolve eq55 eq967526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq967526
  have eq972051 : y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq972012
    | exact resolve eq972012 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq972012
  have eq972057 : y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq972051
       have r₂ := eq50
       grind)
    | exact resolve eq972051 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972051
  have eq972080 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq50126
       have i₂ := eq972057
       grind)
    | exact superpose eq972057 eq50126
    | exact resolve eq50126 eq972057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50126 eq972057
  have eq972116 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq972080
  have eq975144 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq59 y y x
       have i₂ := eq972116
       grind)
    | exact superpose eq972116 eq59
    | exact resolve eq59 eq972116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972116
  have eq977938 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq975144 x
       grind)
    | exact superpose eq975144 eq18
    | (have j1 := eq975144 x
       grind)
    | exact resolve eq18 eq975144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq975144
  have eq977941 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq977938
  have eq980179 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq977941 eq20
    | exact resolve eq20 eq977941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977941
  have eq981046 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq980179
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq980179
    | exact resolve eq980179 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980179
  have eq982974 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq981046 eq26
    | exact resolve eq26 eq981046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981046
  have eq983346 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq274 eq982974
    | exact resolve eq982974 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982974
  have eq983384 : x = (M.op x y) := by
    first
    | (have r₁ := eq983346
       have r₂ := eq27
       grind)
    | exact resolve eq983346 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983346
  have eq983399 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq983384 eq20
    | exact resolve eq20 eq983384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq983401 : x ≠ x ∨ y = (k x y) := by
    first
    | exact superpose eq983384 eq50
    | (have r₁ := eq50
       have r₂ := eq983384
       grind)
    | exact resolve eq50 eq983384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq984130 : y = (k x y) := by grind
  clear eq983401
  have eq984263 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq983399
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq983399
    | exact resolve eq983399 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983399
  have eq984267 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq984263 eq26
    | exact resolve eq26 eq984263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq989850 : (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq27100
       have i₂ := eq984130
       grind)
    | exact superpose eq984130 eq27100
    | exact resolve eq27100 eq984130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27100
  have eq989924 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq983384 eq989850
    | exact resolve eq989850 eq983384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989850
  have eq989976 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq989924
       have i₂ := eq984130
       grind)
    | exact superpose eq984130 eq989924
    | exact resolve eq989924 eq984130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989924
  have eq990027 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq984263 eq989976
    | exact resolve eq989976 eq984263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989976
  have eq990062 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq990027
       have r₂ := eq27
       grind)
    | exact resolve eq990027 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990027
  have eq1007824 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq990062 eq59
    | exact resolve eq59 eq990062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq990062
  have eq1007981 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq984267 eq1007824
    | (have j0 := eq1007824 (σ x)
       grind)
    | exact resolve eq1007824 eq984267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007824
  have eq1008150 : (M.op x y) = (τ (k (σ (M.op x y)) (σ y))) ∨ x = y := by
    first
    | exact superpose eq1007981 eq1063
    | exact resolve eq1063 eq1007981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063 eq1007981
  have eq1011266 : (M.op x y) = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq141 eq1008150
    | exact resolve eq1008150 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq1008150
  have eq1012958 : x = (k x y) ∨ x = y := by
    first
    | exact superpose eq983384 eq1011266
    | exact resolve eq1011266 eq983384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983384 eq1011266
  have eq1015003 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1012958
       have i₂ := eq984130
       grind)
    | exact superpose eq984130 eq1012958
    | exact resolve eq1012958 eq984130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984130 eq1012958
  have eq1015004 : x = y := by grind
  clear eq1015003
  have eq1021492 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1015004
       grind)
    | exact superpose eq1015004 eq24
    | exact resolve eq24 eq1015004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1015004
  have eq1022098 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1021492
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1021492
    | exact resolve eq1021492 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1021492
  have eq1022282 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq984263 eq1022098
    | exact resolve eq1022098 eq984263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984263 eq1022098
  have eq1022765 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1022282 eq984267
    | exact resolve eq984267 eq1022282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984267 eq1022282
  have eq1022778 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq274 eq1022765
    | exact resolve eq1022765 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274 eq1022765
  have eq1022940 : False := by grind
  exact eq1022940

/-- `Equation3583`: `x ◇ y = z ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_x_y_pxy_Equation3583 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3583 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3583.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
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
  clear eq35
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
  have eq175 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 (M.op (M.op X0 X0) X1) X3
       have i₂ := eq16 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq175 X0 X1 x X3
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq178 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq177 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 x y X0
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y) X0
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X2 (M.op X0 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 X1)
       have i₂ := eq177 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq177 eq13
    | (have j0 := eq13 X2 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X1)
       have r₂ := eq177 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq185 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq190 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq178 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq178 (M.op x y)
       grind)
    | exact resolve eq13 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq193 : ∀ X0 : G, (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq190 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq196 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq179 eq13
    | (have j0 := eq13 X0 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 X0 (M.op (σ x) (σ y))
       have r₂ := eq179 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq13 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq199 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq196 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq201 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq193 eq41
    | exact resolve eq41 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq204 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq193 eq37
    | exact resolve eq37 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq205 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq204
    | exact resolve eq204 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq240 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq201 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq201
    | exact resolve eq201 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq411 : x ≠ (M.op x y) ∨ y = (M.op y y) ∨ y = (k x y) := by
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
  have eq412 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq419 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq438 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq439 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq439 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq986 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1034 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq205 eq440
    | (have j0 := eq440 (σ (M.op x y))
       grind)
    | (have r₁ := eq440 (σ (M.op x y))
       have r₂ := eq205
       grind)
    | exact resolve eq440 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq1035 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq1034
  have eq1050 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1035 eq177
    | exact resolve eq177 eq1035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035
  have eq1466 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq986 X0 (M.op X1 X2)
       have i₂ := eq187 X1 X2 (σ X0)
       grind)
    | exact superpose eq187 eq986
    | exact resolve eq986 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq1479 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq199 eq986
    | exact resolve eq986 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq986
  have eq1505 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1479 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1479
    | exact resolve eq1479 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479
  have eq1518 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1466 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1466
    | exact resolve eq1466 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466
  have eq1544 : (τ (M.op (σ x) (σ y))) ≠ (τ (M.op (σ x) (σ y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1505 eq440
    | (have j0 := eq440 (τ (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq440 (τ (M.op (σ x) (σ y)))
       have r₂ := eq1505 (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq440 eq1505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1505
  have eq1553 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by grind
  clear eq1544
  have eq1714 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op X0 (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1553 eq177
    | exact resolve eq177 eq1553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553
  have eq1740 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq418
       grind)
    | exact superpose eq418 eq40
    | exact resolve eq40 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1741 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1740
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1740
    | exact resolve eq1740 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1740
  have eq1743 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1741
    | exact resolve eq1741 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1741
  have eq4671 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1743 eq419
    | exact resolve eq419 eq1743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743
  have eq4680 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq4671
       have r₂ := eq27
       grind)
    | exact resolve eq4671 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4671
  have eq4807 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq4680 eq1518
    | exact resolve eq1518 eq4680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4680
  have eq4839 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq31 eq4807
    | exact resolve eq4807 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4807
  have eq4845 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4839 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq4839 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq4839 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4839
  have eq4857 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq418
       have i₂ := eq4845 x
       grind)
    | exact superpose eq4845 eq418
    | exact resolve eq418 eq4845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4859 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq4845 y
       grind)
    | exact superpose eq4845 eq36
    | exact resolve eq36 eq4845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq4845
  have eq4864 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4857
  have eq4874 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4859
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4859
    | exact resolve eq4859 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4859
  have eq4888 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq177 y y x
       have i₂ := eq4864
       grind)
    | exact superpose eq4864 eq177
    | exact resolve eq177 eq4864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4864
  have eq4949 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4874 eq438
    | (have j0 := eq438 (σ y) (σ y)
       grind)
    | (have r₁ := eq438 (σ y) (σ y)
       have r₂ := eq4874
       grind)
    | exact resolve eq438 eq4874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438 eq4874
  have eq4950 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4949
  have eq4951 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4950
  have eq5053 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4888 x
       grind)
    | exact superpose eq4888 eq18
    | (have j1 := eq4888 x
       grind)
    | exact resolve eq18 eq4888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4888
  have eq5088 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5053 eq412
    | (have r₁ := eq412
       have r₂ := eq5053
       grind)
    | exact resolve eq412 eq5053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq5140 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq5088
  have eq5175 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4951 eq177
    | exact resolve eq177 eq4951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4951
  have eq5280 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5175 eq26
    | (have j1 := eq5175 (σ x)
       grind)
    | exact resolve eq26 eq5175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5175
  have eq5308 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5280 eq27
    | exact resolve eq27 eq5280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7183 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5140 eq90
    | exact resolve eq90 eq5140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq5140
  have eq7196 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq7183
    | exact resolve eq7183 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7183
  have eq7310 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7196 eq177
    | exact resolve eq177 eq7196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7196
  have eq7448 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7310 eq26
    | (have j1 := eq7310 (σ x)
       grind)
    | exact resolve eq26 eq7310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7310
  have eq7451 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5053 eq7448
    | exact resolve eq7448 eq5053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7448
  have eq7479 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq418
       have i₂ := eq7451
       grind)
    | exact superpose eq7451 eq418
    | exact resolve eq418 eq7451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418 eq7451
  have eq7485 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq7479
  have eq7499 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq177 y y x
       have i₂ := eq7485
       grind)
    | exact superpose eq7485 eq177
    | exact resolve eq177 eq7485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7485
  have eq7623 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq7499 x
       grind)
    | exact superpose eq7499 eq18
    | (have j1 := eq7499 x
       grind)
    | exact resolve eq18 eq7499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7499
  have eq7624 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq7623
  have eq7629 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7624 eq31
    | exact resolve eq31 eq7624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7624
  have eq7710 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq7629
    | exact resolve eq7629 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7629
  have eq7729 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq7710
       grind)
    | exact superpose eq7710 eq24
    | exact resolve eq24 eq7710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7710
  have eq7775 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq7729
    | exact resolve eq7729 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7729
  have eq7822 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq7775 eq1050
    | exact resolve eq1050 eq7775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq7834 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7775 eq5308
    | (have r₁ := eq5308
       have r₂ := eq7775
       grind)
    | exact resolve eq5308 eq7775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5308
  have eq7835 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq7834
  have eq7836 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq7835
  have eq7838 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5053 eq7836
    | exact resolve eq7836 eq5053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5053 eq7836
  have eq7839 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq7838
  have eq8197 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7839 eq27
    | exact resolve eq27 eq7839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8238 : ∀ X0 : G, (τ (σ x)) = (M.op X0 (τ (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7839 eq1714
    | exact resolve eq1714 eq7839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8272 : ∀ X0 : G, x = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq8238
    | exact resolve eq8238 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq8238
  have eq8287 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7775 eq8197
    | exact resolve eq8197 eq7775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7775 eq8197
  have eq8288 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq8287
  have eq8993 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7822 eq26
    | (have j1 := eq7822 (σ x)
       grind)
    | exact resolve eq26 eq7822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7822
  have eq8997 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7839 eq8993
    | exact resolve eq8993 eq7839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7839 eq8993
  have eq9022 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq8997
       have r₂ := eq8288
       grind)
    | exact resolve eq8997 eq8288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8288 eq8997
  have eq9043 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq9022
       grind)
    | exact superpose eq9022 eq22
    | exact resolve eq22 eq9022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9049 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y y) ∨ y = (k (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq411
       have i₂ := eq9022
       grind)
    | exact superpose eq9022 eq411
    | (have r₁ := eq411
       have r₂ := eq9022
       grind)
    | exact resolve eq411 eq9022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq9063 : y = (k (M.op x y) y) ∨ y = (M.op y y) ∨ x = y := by grind
  clear eq9049
  have eq9066 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq9043
    | exact resolve eq9043 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9043
  have eq13201 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq9063 eq37
    | exact resolve eq37 eq9063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq9063
  have eq13208 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq13201
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13201
    | exact resolve eq13201 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13201
  have eq13211 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq9066 eq13208
    | exact resolve eq13208 eq9066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13208
  have eq13314 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq13211 eq419
    | exact resolve eq419 eq13211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419 eq13211
  have eq13330 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5280 eq13314
    | exact resolve eq13314 eq5280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5280 eq13314
  have eq22099 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13330 eq1518
    | exact resolve eq1518 eq13330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518 eq13330
  have eq22133 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq31 eq22099
    | exact resolve eq22099 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22099
  have eq22139 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq22133 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq22133 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq22133 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22133
  have eq22153 : y ≠ y ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq440 y
       have i₂ := eq22139 y
       grind)
    | exact superpose eq22139 eq440
    | (have j0 := eq440 y
       grind)
    | (have r₁ := eq440 y
       have r₂ := eq22139 y
       grind)
    | exact resolve eq440 eq22139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440 eq22139
  have eq22181 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq22153
  have eq22219 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq177 y y x
       have i₂ := eq22181
       grind)
    | exact superpose eq22181 eq177
    | exact resolve eq177 eq22181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq22181
  have eq23461 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq22219 x
       grind)
    | exact superpose eq22219 eq18
    | (have j1 := eq22219 x
       grind)
    | exact resolve eq18 eq22219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22219
  have eq23464 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq23461
  have eq23512 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23464 eq1714
    | exact resolve eq1714 eq23464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1714 eq23464
  have eq23548 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq31 eq23512
    | exact resolve eq23512 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq23512
  have eq23800 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq23548 x
       grind)
    | exact superpose eq23548 eq18
    | (have j1 := eq23548 x
       grind)
    | exact resolve eq18 eq23548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23548
  have eq23803 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq23800
  have eq23812 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23803 eq27
    | exact resolve eq27 eq23803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23803
  have eq23902 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq9066 eq23812
    | (have r₁ := eq23812
       have r₂ := eq9066
       grind)
    | exact resolve eq23812 eq9066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9066 eq23812
  have eq23904 : y = (M.op x y) ∨ x = y := by grind
  clear eq23902
  have eq23942 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq23904
  have eq23943 : x = y := by
    first
    | (have r₁ := eq23942
       have r₂ := eq9022
       grind)
    | exact resolve eq23942 eq9022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9022 eq23942
  have eq23950 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq23943
       grind)
    | exact superpose eq23943 eq18
    | exact resolve eq18 eq23943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq23951 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq23943
       grind)
    | exact superpose eq23943 eq24
    | exact resolve eq24 eq23943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq23943
  have eq24029 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq23951
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23951
    | exact resolve eq23951 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23951
  have eq24030 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq24029 eq26
    | exact resolve eq26 eq24029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq24029
  have eq24153 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8272 x
       have i₂ := eq23950
       grind)
    | exact superpose eq23950 eq8272
    | exact resolve eq8272 eq23950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8272 eq23950
  have eq24199 : x = (M.op x y) := by grind
  clear eq24153
  have eq24237 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq24199
       grind)
    | exact superpose eq24199 eq22
    | exact resolve eq22 eq24199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24199
  have eq24330 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq24237 eq20
    | exact resolve eq20 eq24237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq24237
  have eq24515 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq24330 eq240
    | exact resolve eq240 eq24330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq24671 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24030 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq24030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24030
  have eq24708 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24671
  have eq24711 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24515 eq24708
    | exact resolve eq24708 eq24515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24515 eq24708
  have eq24712 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24711
  have eq24718 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq24712 eq27
    | exact resolve eq27 eq24712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq24712
  have eq24808 : False := by grind
  exact eq24808

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_y_y_x_pxy_Equation3600 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3600 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k x y) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq14 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq59 X0 X1 x X3
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq99
    | exact resolve eq99 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq108 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq126 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq143 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq126 eq16
    | exact resolve eq16 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq150 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq127 eq16
    | exact resolve eq16 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq61 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq61
    | (have j0 := eq61 x y X0
       grind)
    | exact resolve eq61 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq61
    | (have j0 := eq61 (σ x) (σ y) X0
       grind)
    | exact resolve eq61 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X2 ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 X1)
       have i₂ := eq61 X0 X1 X2
       grind)
    | exact superpose eq61 eq13
    | (have j0 := eq13 X2 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 (M.op X0 X1) (M.op X0 X1)
       have r₂ := eq61 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op X0 (M.op x y)) = X0 ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq221 eq12
    | (have j0 := eq12 X0 (M.op x y)
       grind)
    | (have r₁ := eq12 X0 (M.op x y)
       have r₂ := eq221 (M.op x y)
       grind)
    | exact resolve eq12 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq221 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq221 (M.op x y)
       grind)
    | exact resolve eq13 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq240 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq247 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq221 eq245
    | (have j0 := eq245 X0
       grind)
    | exact resolve eq245 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq245
  have eq264 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq271 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op X0 (M.op (σ x) (σ y))) = X0 ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq222 eq12
    | (have j0 := eq12 X0 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 X0 (M.op (σ x) (σ y))
       have r₂ := eq222 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq12 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ X0 ∨ (M.op (σ x) (σ y)) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq222 eq13
    | (have j0 := eq13 X0 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (M.op (σ x) (σ y))
       have r₂ := eq222 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq13 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = X0 ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq271 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq278 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ (M.op (σ x) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq222 eq276
    | (have j0 := eq276 X0
       grind)
    | exact resolve eq276 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq276
  have eq309 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq318 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j0 := eq243 (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq321 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq318 eq127
    | exact resolve eq127 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq325 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq321
    | exact resolve eq321 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq328 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq325 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq329 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq328
  have eq333 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq329 eq61
    | exact resolve eq61 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have j0 := eq274 (M.op (σ x) (σ y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq561 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq83 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq662 : ∀ X0 : G, (k (τ X0) (k x y)) = (τ (k X0 (k (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq264 X0 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq264
    | exact resolve eq264 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq756 : ∀ X0 : G, (k (k x y) (τ X0)) = (τ (k (k (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq309 (k x y) X0
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq309
    | exact resolve eq309 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq766 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq20 eq309
    | (have j0 := eq309 (M.op x y) X0
       grind)
    | exact resolve eq309 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ x) (σ y)))) ∨ (σ X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq278 eq309
    | (have j1 := eq278 (σ X0)
       grind)
    | exact resolve eq309 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq309
  have eq785 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (σ y)))) = X0 ∨ (σ X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq774 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq774
    | (have j0 := eq774 X0
       grind)
    | exact resolve eq774 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq1062 : (M.op x y) = (τ (k (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq785 eq766
    | (have j1 := eq785 (M.op x y)
       grind)
    | exact resolve eq766 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766 eq785
  have eq1070 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (k (σ (M.op x y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq20 eq1062
    | exact resolve eq1062 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1079 : (M.op x y) = (τ (k (σ (M.op x y)) (M.op (σ x) (σ y)))) := by
    first
    | (have r₁ := eq1070
       have r₂ := eq27
       grind)
    | exact resolve eq1070 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070
  have eq1084 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1079 eq15
    | exact resolve eq15 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1099 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20 eq1084
    | exact resolve eq1084 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1251 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq234 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq22644 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22652 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq22644
    | exact resolve eq22644 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22644
  have eq22657 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq22652
       have r₂ := eq27
       grind)
    | exact resolve eq22652 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22652
  have eq22659 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq22657
    | exact resolve eq22657 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22657
  have eq26772 : (k (M.op x y) (k x y)) = (τ (k (k (σ (M.op x y)) (M.op (σ x) (σ y))) (k (σ x) (σ y)))) := by
    first
    | exact superpose eq1079 eq662
    | exact resolve eq662 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq26840 : (k (M.op x y) (k x y)) = (τ (k (σ (M.op x y)) (k (σ x) (σ y)))) := by
    first
    | exact superpose eq1099 eq26772
    | exact resolve eq26772 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26772
  have eq26903 : (k (M.op x y) (k x y)) = (τ (k (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26840
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26840
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq26840 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26840
  have eq26938 : (k (M.op x y) (k x y)) = (τ (k (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq26903
    | exact resolve eq26903 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26903
  have eq26940 : (M.op x y) = (k (M.op x y) (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1079 eq26938
    | exact resolve eq26938 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26938
  have eq26942 : (M.op x y) = (k (M.op x y) (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq26940
    | exact resolve eq26940 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26940
  have eq29028 : (k (k x y) (M.op x y)) = (τ (k (k (σ x) (σ y)) (k (σ (M.op x y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq1079 eq756
    | exact resolve eq756 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq29133 : (k (k x y) (M.op x y)) = (τ (k (k (σ x) (σ y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq1099 eq29028
    | exact resolve eq29028 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099 eq29028
  have eq29197 : (τ (k (σ (M.op x y)) (σ (M.op x y)))) = (k (k x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq102 eq29133
    | exact resolve eq29133 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq29133
  have eq29256 : (k (M.op x y) (M.op x y)) = (k (k x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq150 eq29197
    | exact resolve eq29197 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq29197
  have eq29261 : (M.op x y) = (k (k x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq318 eq29256
    | exact resolve eq29256 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318 eq29256
  have eq67829 : (M.op x y) = (k x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29261 eq247
    | (have j0 := eq247 (k x y)
       grind)
    | exact resolve eq247 eq29261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq29261
  have eq67835 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq67829
  have eq1185601 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq22659 eq61
    | exact resolve eq61 eq22659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22659
  have eq1185686 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1185601
    | (have j0 := eq1185601 (σ x)
       grind)
    | exact resolve eq1185601 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185601
  have eq1187646 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1251 y y
       have i₂ := eq1185686
       grind)
    | exact superpose eq1185686 eq1251
    | exact resolve eq1251 eq1185686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251 eq1185686
  have eq1194762 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq561 y y
       have i₂ := eq1187646
       grind)
    | exact superpose eq1187646 eq561
    | (have j0 := eq561 y y
       grind)
    | exact resolve eq561 eq1187646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561 eq1187646
  have eq1194820 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1194762
  have eq1194821 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1194820
  have eq1194850 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1194821
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1194821
    | exact resolve eq1194821 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194821
  have eq1197293 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1194850 eq61
    | exact resolve eq61 eq1194850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194850
  have eq1201708 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1197293 eq26
    | (have j1 := eq1197293 (σ x)
       grind)
    | exact resolve eq26 eq1197293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197293
  have eq1201709 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1201708
  have eq1201733 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1201709 eq431
    | exact resolve eq431 eq1201709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431 eq1201709
  have eq1209743 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1201733 eq108
    | exact resolve eq108 eq1201733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq1201733
  have eq1209844 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1209743
    | exact resolve eq1209743 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209743
  have eq1213798 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq1209844
       grind)
    | exact superpose eq1209844 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq1209844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209844
  have eq1213861 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1213798
  have eq1213972 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq61 y y x
       have i₂ := eq1213861
       grind)
    | exact superpose eq1213861 eq61
    | exact resolve eq61 eq1213861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213861
  have eq1215796 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1213972 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1213972
    | (have j0 := eq1213972 x
       grind)
    | exact resolve eq1213972 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213972
  have eq1217697 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1215796 eq51
    | (have r₁ := eq51
       have r₂ := eq1215796
       grind)
    | exact resolve eq51 eq1215796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1215796
  have eq1219278 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1217697
  have eq1228737 : (τ (σ y)) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1219278 eq55
    | exact resolve eq55 eq1219278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1219278
  have eq1228795 : y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1228737
    | exact resolve eq1228737 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1228737
  have eq1228801 : y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1228795
       have r₂ := eq50
       grind)
    | exact resolve eq1228795 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228795
  have eq1228827 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq67835
       have i₂ := eq1228801
       grind)
    | exact superpose eq1228801 eq67835
    | exact resolve eq67835 eq1228801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67835 eq1228801
  have eq1228886 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1228827
  have eq1240602 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq61 y y x
       have i₂ := eq1228886
       grind)
    | exact superpose eq1228886 eq61
    | exact resolve eq61 eq1228886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228886
  have eq1241135 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1240602 x
       grind)
    | exact superpose eq1240602 eq18
    | (have j1 := eq1240602 x
       grind)
    | exact resolve eq18 eq1240602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1240602
  have eq1241138 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1241135
  have eq1241157 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1241138 eq20
    | exact resolve eq20 eq1241138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241138
  have eq1242041 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1241157
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1241157
    | exact resolve eq1241157 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241157
  have eq1242045 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1242041 eq26
    | exact resolve eq26 eq1242041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242041
  have eq1242480 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq333 eq1242045
    | exact resolve eq1242045 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333 eq1242045
  have eq1242530 : x = (M.op x y) := by
    first
    | (have r₁ := eq1242480
       have r₂ := eq27
       grind)
    | exact resolve eq1242480 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242480
  have eq1242551 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1242530 eq20
    | exact resolve eq20 eq1242530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1242553 : x ≠ x ∨ y = (k x y) := by
    first
    | exact superpose eq1242530 eq50
    | (have r₁ := eq50
       have r₂ := eq1242530
       grind)
    | exact resolve eq50 eq1242530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1243299 : y = (k x y) := by grind
  clear eq1242553
  have eq1243433 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1242551
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1242551
    | exact resolve eq1242551 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242551
  have eq1243437 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1243433 eq26
    | exact resolve eq26 eq1243433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1244584 : (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26942
       have i₂ := eq1243299
       grind)
    | exact superpose eq1243299 eq26942
    | exact resolve eq26942 eq1243299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26942
  have eq1244689 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1242530 eq1244584
    | exact resolve eq1244584 eq1242530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244584
  have eq1244751 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1244689
       have i₂ := eq1243299
       grind)
    | exact superpose eq1243299 eq1244689
    | exact resolve eq1244689 eq1243299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244689
  have eq1244812 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1243433 eq1244751
    | exact resolve eq1244751 eq1243433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244751
  have eq1244851 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq1244812
       have r₂ := eq27
       grind)
    | exact resolve eq1244812 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244812
  have eq1248020 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1244851 eq61
    | exact resolve eq61 eq1244851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq1244851
  have eq1248244 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1243437 eq1248020
    | (have j0 := eq1248020 (σ x)
       grind)
    | exact resolve eq1248020 eq1243437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248020
  have eq1248405 : (M.op x y) = (τ (k (σ (M.op x y)) (σ y))) ∨ x = y := by
    first
    | exact superpose eq1248244 eq1079
    | exact resolve eq1079 eq1248244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079 eq1248244
  have eq1251496 : (M.op x y) = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq143 eq1248405
    | exact resolve eq1248405 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq1248405
  have eq1253171 : x = (k x y) ∨ x = y := by
    first
    | exact superpose eq1242530 eq1251496
    | exact resolve eq1251496 eq1242530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242530 eq1251496
  have eq1255202 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1253171
       have i₂ := eq1243299
       grind)
    | exact superpose eq1243299 eq1253171
    | exact resolve eq1253171 eq1243299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243299 eq1253171
  have eq1255203 : x = y := by grind
  clear eq1255202
  have eq1256780 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1255203
       grind)
    | exact superpose eq1255203 eq24
    | exact resolve eq24 eq1255203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1255203
  have eq1257425 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1256780
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1256780
    | exact resolve eq1256780 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1256780
  have eq1257622 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1243433 eq1257425
    | exact resolve eq1257425 eq1243433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243433 eq1257425
  have eq1258166 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1257622 eq1243437
    | exact resolve eq1243437 eq1257622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243437 eq1257622
  have eq1258179 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq329 eq1258166
    | exact resolve eq1258166 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329 eq1258166
  have eq1258375 : False := by grind
  exact eq1258375

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_x_pyy_pxy_Equation3600 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3600 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq9 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq62 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq65 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq64 (M.op X1 X0) X1 x
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X1 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X1 X0)
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (M.op X1 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq65 X0 X0
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq78 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq71 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq82 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 (M.op X0 X1)
       have i₂ := eq64 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq64 eq78
    | exact resolve eq78 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq571 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq577 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq571 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq571
    | (have j0 := eq571 (σ X0)
       grind)
    | exact resolve eq571 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq571 (τ X0)
       grind)
    | exact superpose eq571 eq17
    | (have j1 := eq571 (τ X0)
       grind)
    | exact resolve eq17 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq571
  have eq602 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq595 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq595
    | (have j0 := eq595 X0
       grind)
    | exact resolve eq595 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq634 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq577 (M.op X0 X1)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq577
    | (have j0 := eq577 (M.op X0 X1)
       grind)
    | exact resolve eq577 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq657 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq634 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq692 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
       have i₂ := eq657 X0 X1
       grind)
    | exact superpose eq657 eq64
    | exact resolve eq64 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq868 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq602 X0
       grind)
    | exact superpose eq602 eq10
    | (have j1 := eq602 X0
       grind)
    | exact resolve eq10 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq1479 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq1561 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq868 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq1594 : ∀ X0 X1 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1561 (M.op X0 X1)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq1561
    | (have j0 := eq1561 (M.op X0 X1)
       grind)
    | exact resolve eq1561 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq1561
  have eq1599 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1594 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594
  have eq1634 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 (τ (M.op X0 X1)) (τ (M.op X0 X1)) x
       have i₂ := eq1599 X0 X1
       grind)
    | exact superpose eq1599 eq64
    | exact resolve eq64 eq1599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1599
  have eq2340 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq1479 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq1479 X0 X1
       grind)
    | exact superpose eq1479 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq1479 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq1479 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq1479 X0 X0
       grind)
    | exact resolve eq13 eq1479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479
  have eq2395 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2340 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2340
  have eq2396 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2395 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2395
  have eq2400 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2396 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2396
    | (have j0 := eq2396 X0 X1
       grind)
    | exact resolve eq2396 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2396
  have eq12714 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2400 (τ X0) (τ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq2400
    | (have j0 := eq2400 (τ X1) (τ X0)
       grind)
    | exact resolve eq2400 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2400
  have eq12854 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12714 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq12714
    | (have j0 := eq12714 X0 X1
       grind)
    | exact resolve eq12714 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12714
  have eq12891 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12854 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12854
    | (have j0 := eq12854 X0 X1
       grind)
    | exact resolve eq12854 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12854
  have eq12922 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12891 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq12891
    | (have j0 := eq12891 X0 X1
       grind)
    | exact resolve eq12891 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12891
  have eq12936 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12922 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12922
    | (have j0 := eq12922 X0 X1
       grind)
    | exact resolve eq12922 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12922
  have eq12944 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12936 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12936
    | (have j0 := eq12936 X0 X1
       grind)
    | exact resolve eq12936 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12936
  have eq12955 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (k X0 X1))) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12944 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12944
    | (have j0 := eq12944 X0 X1
       grind)
    | exact resolve eq12944 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12944
  have eq12960 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12955 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq12955
    | (have j0 := eq12955 X0 X1
       grind)
    | exact resolve eq12955 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12955
  have eq13341 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq12960 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12960
  have eq13358 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13341 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13341 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13341 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13341 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13341 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13341
  have eq13521 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13358 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq13358
    | (have j0 := eq13358 (σ X0) (σ X1)
       grind)
    | exact resolve eq13358 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13751 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq13521 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13521
  have eq13752 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13751 X0 X1
       have i₂ := eq13358 X0 X1
       grind)
    | exact superpose eq13358 eq13751
    | (have j0 := eq13751 X0 X1
       have j1 := eq13358 (σ X0) (σ X1)
       grind)
    | exact resolve eq13751 eq13358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13358 eq13751
  have eq239631 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13752 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13752
  have eq239767 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq239631 x y
       grind)
    | exact superpose eq239631 eq16
    | (have j1 := eq239631 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq239631 x y
       grind)
    | exact resolve eq16 eq239631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239631
  have eq239977 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq239767
  have eq240322 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1634 (σ y) (σ x) x
       have i₂ := eq239977
       grind)
    | exact superpose eq239977 eq1634
    | exact resolve eq1634 eq239977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1634 eq239977
  have eq240490 : ∀ X0 : G, y = (M.op y x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq240322 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq240322
    | exact resolve eq240322 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240322
  have eq240588 : ∀ X0 X1 : G, y = (M.op X1 y) ∨ y = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq64 y x x
       have i₂ := eq240490 X0
       grind)
    | exact superpose eq240490 eq64
    | (have j1 := eq240490 X1
       grind)
    | exact resolve eq64 eq240490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq240490
  have eq240885 : ∀ X0 : G, y ≠ y ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq240588 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240588
  have eq240886 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq240885 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240885
  have eq241008 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq240886 x
       grind)
    | exact superpose eq240886 eq16
    | exact resolve eq16 eq240886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241047 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) := by
    intro X1
    first
    | (have i₁ := eq692 x y x
       have i₂ := eq240886 x
       grind)
    | exact superpose eq240886 eq692
    | exact resolve eq692 eq240886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692 eq240886
  have eq242246 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq241008
       have i₂ := eq241047 (σ x)
       grind)
    | exact superpose eq241047 eq241008
    | (have r₁ := eq241008
       have r₂ := eq241047 (σ x)
       grind)
    | exact resolve eq241008 eq241047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241008 eq241047
  have eq242452 : False := by grind
  exact eq242452

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxy_pxx_pyx_Equation3600 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3600 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  clear eq18
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
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq109 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq9 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq109 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq109
    | exact resolve eq109 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq111 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq110 (σ X0) (σ X0) x
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq110
    | exact resolve eq110 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq110 (τ X0) (τ X0) x
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq110
    | exact resolve eq110 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq135 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq111 (M.op X0 X1) X1
       have i₂ := eq110 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq110 eq111
    | exact resolve eq111 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq168 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq112 (M.op X0 X1) X1
       have i₂ := eq110 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq110 eq112
    | exact resolve eq112 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq680 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq681 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq1062 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq681 x y
       grind)
    | exact superpose eq681 eq16
    | (have j1 := eq681 x y
       grind)
    | exact resolve eq16 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq7278 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq680 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq680
    | exact resolve eq680 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq7414 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7278 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq7278
    | (have j0 := eq7278 X0 X1
       grind)
    | exact resolve eq7278 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7278
  have eq20132 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1062
       have i₂ := eq7414 x y
       grind)
    | exact superpose eq7414 eq1062
    | (have j1 := eq7414 (σ x) (σ y)
       grind)
    | (have r₁ := eq1062
       have r₂ := eq7414 x y
       grind)
    | (have r₁ := eq1062
       have r₂ := eq7414 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1062
       have r₂ := eq7414 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1062 eq7414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062 eq7414
  have eq20133 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq20132
  have eq155493 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20133
       grind)
    | exact superpose eq20133 eq16
    | exact resolve eq16 eq20133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20133
  have eq155506 : (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq155493
       have r₂ := eq22 x
       grind)
    | exact resolve eq155493 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155493
  have eq155508 : y = (τ (σ x)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq155506
       grind)
    | exact superpose eq155506 eq10
    | exact resolve eq10 eq155506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155506
  have eq155604 : x = y ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq155508
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq155508
    | exact resolve eq155508 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155508
  have eq155606 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq155604
       grind)
    | exact superpose eq155604 eq16
    | exact resolve eq16 eq155604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155604
  have eq155619 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq155606
       have r₂ := eq22 x
       grind)
    | exact resolve eq155606 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq155606
  have eq155640 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq110 y x x
       have i₂ := eq155619
       grind)
    | exact superpose eq155619 eq110
    | exact resolve eq110 eq155619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq155619
  have eq155815 : ∀ X0 X1 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq168 (σ y) (σ x) x
       have i₂ := eq155640 X0
       grind)
    | exact superpose eq155640 eq168
    | (have j1 := eq155640 X1
       grind)
    | exact resolve eq168 eq155640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq155640
  have eq155976 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq155815 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq155815
    | (have j0 := eq155815 X0 X0
       grind)
    | exact resolve eq155815 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155815
  have eq156397 : ∀ X0 : G, y ≠ y ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq155976 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155976
  have eq156398 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq156397 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156397
  have eq156611 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) := by
    intro X1
    first
    | (have i₁ := eq135 x y x
       have i₂ := eq156398 x
       grind)
    | exact superpose eq156398 eq135
    | exact resolve eq135 eq156398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq157197 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq156611 (σ x)
       grind)
    | exact superpose eq156611 eq16
    | exact resolve eq16 eq156611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156611
  have eq157248 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq157197
       have i₂ := eq156398 x
       grind)
    | exact superpose eq156398 eq157197
    | exact resolve eq157197 eq156398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156398 eq157197
  have eq157249 : False := by grind
  exact eq157249

/-- `Equation3601`: `x ◇ y = z ◇ ((y ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pxy_pyx_pxy_Equation3601 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3601 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3601.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
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
  clear eq18
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) X2) X2) = (M.op X3 (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) X2) X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X1 X0) (M.op X3 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X3 (M.op (M.op X1 X0) (M.op X3 X2))
       have i₂ := eq9 X0 X1 (M.op X3 X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 X1 X2 x
       have i₂ := eq9 X1 X0 x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq67 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 X1) (M.op (M.op X1 X0) (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64 X3 X2 (M.op (M.op X1 X0) (M.op X2 X3))
       have i₂ := eq9 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq87 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X2 X3)) = (M.op (M.op X3 X2) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X2 X3) (M.op X3 X2)
       have i₂ := eq63 X3 X2 X0 X1
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X2)) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X2)) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq247 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq247 X1 X1 X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq247 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq247 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq278 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq272 X1 X2 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq272 X0 X1 X2
       have i₂ := eq14 (M.op X0 X2) X1
       grind)
    | exact superpose eq14 eq272
    | (have j0 := eq272 X1 X2 X2
       have j1 := eq14 X0 X1
       grind)
    | exact resolve eq272 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq315 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq278 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq318 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k X1 X2) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq315 X0 X1 X2
       have j1 := eq12 X1 X2
       grind)
    | (have r₁ := eq315 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq315 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq387 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq318 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq388 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq387 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq399 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq388 (σ X0)
       grind)
    | exact superpose eq388 eq15
    | exact resolve eq15 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq401 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq388 (τ X0)
       grind)
    | exact superpose eq388 eq32
    | exact resolve eq32 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq412 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq401 X0
       have i₂ := eq388 X0
       grind)
    | exact superpose eq388 eq401
    | exact resolve eq401 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq414 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq399 X0
       have i₂ := eq388 X0
       grind)
    | exact superpose eq388 eq399
    | exact resolve eq399 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq453 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (M.op (τ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) (τ X0) x
       have i₂ := eq412 X0
       grind)
    | exact superpose eq412 eq9
    | exact resolve eq9 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq478 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) x
       have i₂ := eq414 X0
       grind)
    | exact superpose eq414 eq9
    | exact resolve eq9 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq489 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq414 X0
       grind)
    | exact superpose eq414 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq489 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq489 X0 (M.op (σ (M.op X0 X0)) X0)
       have r₂ := eq12 X0 (σ (M.op X0 X0))
       grind)
    | (have r₁ := eq489 X0 X0
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq489 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq502 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (M.op (τ (M.op X1 X1)) X0) ∨ (M.op X0 (τ (M.op X1 X1))) = (k X0 (τ (M.op X1 X1))) ∨ (τ (M.op X1 X1)) = (M.op (τ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq453 X1 (τ (M.op X1 X1))
       have i₂ := eq14 X0 (τ (M.op X1 X1))
       grind)
    | (have i₁ := eq453 X0 X1
       have i₂ := eq14 (M.op (τ (M.op X0 X0)) X1) X1
       grind)
    | exact superpose eq14 eq453
    | (have j1 := eq14 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq453 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq518 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (M.op (τ (M.op X1 X1)) X0) ∨ (M.op X0 (τ (M.op X1 X1))) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq502 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq527 : ∀ X0 X1 : G, (M.op X0 (τ (M.op X1 X1))) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq518 X0 X1
       have j1 := eq12 X0 (τ (M.op X1 X1))
       grind)
    | (have r₁ := eq518 X0 X1
       have r₂ := eq12 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq518 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq574 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ (M.op X1 X1)) X0) ∨ (M.op X0 (σ (M.op X1 X1))) = (k X0 (σ (M.op X1 X1))) ∨ (σ (M.op X1 X1)) = (M.op (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq478 X1 (σ (M.op X1 X1))
       have i₂ := eq14 X0 (σ (M.op X1 X1))
       grind)
    | (have i₁ := eq478 X0 X1
       have i₂ := eq14 (M.op (σ (M.op X0 X0)) X1) X1
       grind)
    | exact superpose eq14 eq478
    | (have j1 := eq14 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq478 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq592 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ (M.op X1 X1)) X0) ∨ (M.op X0 (σ (M.op X1 X1))) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq574 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq601 : ∀ X0 X1 : G, (M.op X0 (σ (M.op X1 X1))) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq592 X0 X1
       have j1 := eq12 X0 (σ (M.op X1 X1))
       grind)
    | (have r₁ := eq592 X0 X1
       have r₂ := eq12 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq592 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq643 : ∀ X0 X1 : G, (M.op X1 (τ (σ (M.op X0 X0)))) = (k X1 (τ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq527 X0 (σ X0)
       have i₂ := eq414 X0
       grind)
    | exact superpose eq414 eq527
    | exact resolve eq527 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq666 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq643 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq643
    | exact resolve eq643 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq707 : ∀ X0 X1 : G, (σ (k X0 (M.op X1 X1))) = (M.op (σ X0) (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 (M.op X1 X1)
       have i₂ := eq601 (σ X0) X1
       grind)
    | exact superpose eq601 eq15
    | exact resolve eq15 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq715 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X1 X1))) = (σ (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq707 X0 X1
       have i₂ := eq666 X1 X0
       grind)
    | exact superpose eq666 eq707
    | exact resolve eq707 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666 eq707
  have eq864 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq889 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq864 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq898 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq889 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq889 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq889 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889
  have eq962 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq898 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq963 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq898 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq981 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq962 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq962 X0 X1
       have i₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact superpose eq14 eq962
    | (have j0 := eq962 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq962 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq962 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq994 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq981 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq1007 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq994 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq994 (M.op (k X1 X1) X0) X1
       have r₂ := eq12 X0 (k X1 X1)
       grind)
    | (have r₁ := eq994 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq994 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994
  have eq1022 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1007 X0 X1
       have i₂ := eq388 X1
       grind)
    | exact superpose eq388 eq1007
    | (have j0 := eq1007 X0 X1
       grind)
    | exact resolve eq1007 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388 eq1007
  have eq1423 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op X3 X2) (M.op (M.op X2 X3) (M.op X1 X0))) ∨ (M.op (M.op X3 X2) (M.op (M.op X2 X3) (M.op X1 X0))) = (k (M.op (M.op X2 X3) (M.op X1 X0)) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq963 (M.op (M.op X2 X3) (M.op X1 X0)) (M.op X3 X2)
       have i₂ := eq63 X3 X2 X0 X1
       grind)
    | exact superpose eq63 eq963
    | (have j0 := eq963 (M.op (M.op X2 X3) (M.op X1 X0)) (M.op X3 X2)
       grind)
    | exact resolve eq963 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq963
  have eq1464 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op (M.op X3 X2) (M.op (M.op X2 X3) (M.op X1 X0))) = (k (M.op (M.op X2 X3) (M.op X1 X0)) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1423 X0 X1 X2 X3
       have i₂ := eq67 X3 X2 X1 X0
       grind)
    | exact superpose eq67 eq1423
    | (have j0 := eq1423 X0 X1 X2 X3
       grind)
    | (have r₁ := eq1423 X2 X2 X1 X0
       have r₂ := eq67 X0 X1 X2 X2
       grind)
    | exact resolve eq1423 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1423
  have eq1474 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (k (M.op (M.op X2 X3) (M.op X1 X0)) (M.op X3 X2)) ∨ (M.op X0 X1) ≠ (M.op X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1464 X0 X1 X2 X3
       have i₂ := eq67 X3 X2 X1 X0
       grind)
    | exact superpose eq67 eq1464
    | (have j0 := eq1464 X0 X1 X2 X3
       grind)
    | exact resolve eq1464 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1464
  have eq2508 : ∀ X0 X1 X2 X3 : G, (M.op (σ (M.op X0 (M.op X1 X1))) (M.op X3 X2)) = (M.op (M.op X2 X3) (M.op (σ (M.op X1 X1)) (σ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq87 X3 X2 (σ (M.op X1 X1)) (σ X0)
       have i₂ := eq715 X0 X1
       grind)
    | exact superpose eq715 eq87
    | exact resolve eq87 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2606 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (M.op X0 X1) (M.op X0 X1))) = (k (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    grind
  have eq2657 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2606 X0 X1
       have i₂ := eq67 X1 X0 X0 X1
       grind)
    | exact superpose eq67 eq2606
    | (have j0 := eq2606 X0 X1
       grind)
    | exact resolve eq2606 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2606
  have eq2702 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2657 X0 X1
       have i₂ := eq67 X1 X0 X0 X1
       grind)
    | exact superpose eq67 eq2657
    | (have j0 := eq2657 X0 X1
       grind)
    | exact resolve eq2657 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq2657
  have eq2704 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2702 X0 X1
       have j1 := eq1474 X1 X0 X0 X1
       grind)
    | (have r₁ := eq2702 X0 X1
       have r₂ := eq1474 X0 X1 x x
       grind)
    | (have r₁ := eq2702 X1 X0
       have r₂ := eq1474 X0 X1 x x
       grind)
    | exact resolve eq2702 eq1474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474 eq2702
  have eq3192 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2704 X1 X0
       have i₂ := eq87 X0 X1 X1 X0
       grind)
    | (have i₁ := eq2704 X1 X0
       have i₂ := eq87 X1 X0 X0 X1
       grind)
    | exact superpose eq87 eq2704
    | exact resolve eq2704 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq3210 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (σ X0)) = (k (M.op (M.op (σ (M.op X1 X1)) (σ X0)) (M.op (σ (M.op X1 X1)) (σ X0))) (σ (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2704 (σ (M.op X1 X1)) (σ X0)
       have i₂ := eq715 X0 X1
       grind)
    | exact superpose eq715 eq2704
    | exact resolve eq2704 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2704
  have eq3242 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (σ X0)) = (k (M.op (σ (M.op X0 (M.op X1 X1))) (M.op (σ X0) (σ (M.op X1 X1)))) (σ (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3210 X0 X1
       have i₂ := eq2508 X0 X1 (σ (M.op X1 X1)) (σ X0)
       grind)
    | exact superpose eq2508 eq3210
    | exact resolve eq3210 eq2508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2508 eq3210
  have eq3265 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (σ X0)) = (k (M.op (σ (M.op X0 (M.op X1 X1))) (σ (M.op X0 (M.op X1 X1)))) (σ (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3242 X0 X1
       have i₂ := eq715 X0 X1
       grind)
    | exact superpose eq715 eq3242
    | exact resolve eq3242 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715 eq3242
  have eq3273 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (σ X0)) = (k (σ (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) (σ (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3265 X0 X1
       have i₂ := eq414 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq414 eq3265
    | exact resolve eq3265 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414 eq3265
  have eq3281 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (σ X0)) = (σ (k (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3273 X0 X1
       have i₂ := eq15 (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq15 eq3273
    | exact resolve eq3273 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3273
  have eq3286 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (σ X0)) = (σ (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3281 X0 X1
       have i₂ := eq3192 X0 (M.op X1 X1)
       grind)
    | exact superpose eq3192 eq3281
    | exact resolve eq3281 eq3192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3192 eq3281
  have eq4942 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq490 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq490 X0 (σ X0)
       grind)
    | exact superpose eq490 eq10
    | (have j1 := eq490 X1 X0
       grind)
    | exact resolve eq10 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq6614 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq4942 (σ X0) X1
       grind)
    | exact superpose eq4942 eq15
    | (have j1 := eq4942 (σ X0) X1
       grind)
    | exact resolve eq15 eq4942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4942
  have eq6628 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6614 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6614
    | (have j0 := eq6614 X0 X1
       grind)
    | exact resolve eq6614 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6614
  have eq8497 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6628 X0 X1
       have i₂ := eq1022 X0 X1
       grind)
    | exact superpose eq1022 eq6628
    | (have j0 := eq6628 X0 X1
       have j1 := eq1022 X0 X1
       grind)
    | exact resolve eq6628 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022 eq6628
  have eq8686 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq8497 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8497
  have eq11905 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8686 x y
       grind)
    | exact superpose eq8686 eq16
    | (have j1 := eq8686 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq8686 x y
       grind)
    | exact resolve eq16 eq8686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8686
  have eq12147 : x = (M.op y y) := by grind
  clear eq11905
  have eq12290 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3286 X0 y
       have i₂ := eq12147
       grind)
    | exact superpose eq12147 eq3286
    | exact resolve eq3286 eq12147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3286 eq12147
  have eq12355 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12290 y
       grind)
    | exact superpose eq12290 eq16
    | (have r₁ := eq16
       have r₂ := eq12290 y
       grind)
    | exact resolve eq16 eq12290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12290
  have eq12364 : False := by grind
  exact eq12364
