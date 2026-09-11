import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_pxx_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq175 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op (M.op X0 x) (M.op (M.op x y) y)) = X0 := by
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
  have eq179 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 (M.op (M.op X2 X3) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 (M.op X0 X2) (M.op (M.op X2 X3) X3)
       have i₂ := eq16 X0 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op x (M.op (M.op y X1) X1))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 x)) (M.op X0 (M.op (M.op x y) y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq373 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X0 X1 : G, (M.op (k (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X1) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X0 X0) X1
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
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
  have eq554 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq182 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq182
    | (have j1 := eq28 (k X0 X0) X0
       grind)
    | exact resolve eq182 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op (M.op X0 X2) X2)) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq576 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq552
       grind)
    | exact superpose eq552 eq40
    | exact resolve eq40 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq586 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq585
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq585
    | exact resolve eq585 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq588 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq586
    | exact resolve eq586 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq596 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq588 eq554
    | exact resolve eq554 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq596
       have r₂ := eq27
       grind)
    | exact resolve eq596 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq607 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (σ y) (σ y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq603 eq179
    | exact resolve eq179 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq608 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (M.op (σ y) X0) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq603 eq176
    | exact resolve eq176 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq603 eq27
    | exact resolve eq27 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : ∀ X0 : G, (M.op (k (σ x) X0) (M.op (σ y) (σ y))) = X0 ∨ y = (M.op x y) ∨ (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq607 x
       have i₂ := eq28 sF2 x
       grind)
    | exact superpose eq28 eq607
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq607 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : ∀ X0 : G, (k (M.op (σ y) (σ y)) (M.op X0 (σ x))) = X0 ∨ (M.op (σ y) (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq607 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq614 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (σ x))) (M.op X0 (M.op (σ y) (σ y)))) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq607 eq16
    | exact resolve eq16 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq615 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (M.op (σ y) (σ y)) X1) X1)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq607 eq16
    | exact resolve eq16 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq616 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) (M.op (M.op (σ y) X0) X0))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq608 eq608
    | exact resolve eq608 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (M.op (M.op (σ y) X1) X1))) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq608 eq16
    | exact resolve eq16 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq625 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) (M.op (M.op (σ y) X0) X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq616 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq631 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (M.op (σ y) X0) X0))))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq625 eq625
    | exact resolve eq625 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq637 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (M.op (M.op (σ y) X0) X0)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq625 eq608
    | exact resolve eq608 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608 eq625
  have eq642 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (M.op (M.op (σ y) X0) X0)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq637 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq643 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (M.op (σ y) X0) X0))))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq631 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq657 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (M.op X0 (σ x)) (σ x))) X0) = X1 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq607 eq614
    | exact resolve eq614 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq662 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (M.op X0 (σ x)) (σ x))) X0) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq657 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq679 : ∀ X0 X1 : G, (k X1 (M.op X0 (M.op (M.op X1 (σ x)) (σ x)))) = X0 ∨ X0 = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq662 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq681 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (σ x)) (σ x))) = (M.op X0 (M.op (M.op X1 X2) X2)) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq662 eq16
    | exact resolve eq16 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq717 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ y) (σ y))) (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq615 eq16
    | exact resolve eq16 eq615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq767 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ (k y x) = (M.op y y) := by
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
  have eq769 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq576 (σ X1) (σ X0)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq576
    | (have j0 := eq576 (σ X1) (σ X0)
       grind)
    | exact resolve eq576 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq840 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (σ x)) (σ x))) = (M.op X0 (M.op (σ x) (M.op (M.op (σ y) X1) X1))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq662 eq623
    | exact resolve eq623 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623 eq662
  have eq863 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (σ x)) (σ x))) = (M.op X0 (M.op (σ x) (M.op (M.op (σ y) X1) X1))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq840 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq884 : ∀ X0 : G, (σ x) = (k (M.op (σ x) (M.op (σ x) (M.op (M.op (σ y) X0) X0))) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (M.op (M.op (σ y) X0) X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq642 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq897 : ∀ X0 : G, (σ x) = (k (M.op (σ x) (M.op (M.op (σ y) (σ x)) (σ x))) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (M.op (M.op (σ y) X0) X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq863 eq884
    | (have j0 := eq884 X0
       grind)
    | exact resolve eq884 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884
  have eq2124 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op x y) y)) x) = X0 := by
    intro X0
    first
    | exact superpose eq175 eq180
    | exact resolve eq180 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2685 : ∀ X0 : G, (σ x) = (k (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (M.op (σ y) X0) X0)))) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (M.op (σ y) X0) X0)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq643 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq2717 : ∀ X0 : G, (σ x) = (k (M.op (σ x) (M.op (σ x) (M.op (M.op (σ y) (σ x)) (σ x)))) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (M.op (σ y) X0) X0)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq863 eq2685
    | (have j0 := eq2685 X0
       grind)
    | exact resolve eq2685 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2685
  have eq2753 : ∀ X0 : G, (σ x) = (k (M.op (σ x) (M.op (M.op (σ y) (σ x)) (σ x))) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (M.op (M.op (σ y) X0) X0)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq863 eq2717
    | (have j0 := eq2717 X0
       grind)
    | exact resolve eq2717 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863 eq2717
  have eq2774 : (σ x) = (k (M.op (σ x) (M.op (M.op (σ y) (σ x)) (σ x))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq897 eq2753
    | exact resolve eq2753 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897 eq2753
  have eq3398 : ∀ X0 X1 X2 : G, (k X1 (M.op X0 (M.op (M.op X1 X2) X2))) = X0 ∨ X0 = X1 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq679 X0 X1
       have i₂ := eq681 X0 X1 sF2
       grind)
    | exact superpose eq681 eq679
    | (have j0 := eq679 (k X1 (M.op X0 (M.op (M.op X1 X2) X2))) X0
       grind)
    | exact resolve eq679 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679 eq681
  have eq3646 : ∀ X0 X1 X2 : G, (k X1 (M.op X0 (M.op (M.op X1 X2) X2))) = X0 ∨ X0 = X1 ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3398 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3398
  have eq5797 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq603 eq769
    | (have r₁ := eq769
       have r₂ := eq603
       grind)
    | exact resolve eq769 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq5798 : (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5797
  have eq5799 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq588 eq5798
    | exact resolve eq5798 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5798
  have eq5815 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5799 eq182
    | exact resolve eq182 eq5799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5799
  have eq5846 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq5815
    | exact resolve eq5815 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5815
  have eq5851 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq588 eq5846
    | exact resolve eq5846 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588 eq5846
  have eq5854 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq5851
       have r₂ := eq27
       grind)
    | exact resolve eq5851 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5851
  have eq5856 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ (M.op x y))) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5854 eq607
    | exact resolve eq607 eq5854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq5857 : ∀ X0 : G, (M.op (k (σ x) X0) (σ (M.op x y))) = X0 ∨ y = (M.op x y) ∨ (σ x) = (M.op X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5854 eq610
    | (have j0 := eq610 X0
       grind)
    | exact resolve eq610 eq5854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq5858 : ∀ X0 : G, (k (σ (M.op x y)) (M.op X0 (σ x))) = X0 ∨ (σ (M.op x y)) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5854 eq613
    | exact resolve eq613 eq5854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq5865 : ∀ X0 : G, (M.op (M.op X0 (σ (M.op x y))) (σ x)) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5854 eq717
    | exact resolve eq717 eq5854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq5893 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (M.op (σ y) X0) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5854 eq16
    | exact resolve eq16 eq5854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5895 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5854 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq5854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5901 : ∀ X0 : G, (k (σ y) (M.op X0 (M.op (σ (M.op x y)) (σ y)))) = X0 ∨ (σ y) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5854 eq3646
    | (have j0 := eq3646 (k (σ y) (M.op X0 (M.op (σ (M.op x y)) (σ y)))) X0 x
       grind)
    | exact resolve eq3646 eq5854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3646
  have eq5906 : ∀ X0 : G, (k (σ y) (M.op X0 (M.op (σ (M.op x y)) (σ y)))) = X0 ∨ (σ y) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq5901 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5901
  have eq5932 : ∀ X0 : G, (M.op (M.op X0 (σ (M.op x y))) (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq5865 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5865
  have eq5939 : ∀ X0 : G, (k (σ (M.op x y)) (M.op X0 (σ x))) = X0 ∨ (σ (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq5858 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5858
  have eq5940 : ∀ X0 : G, (M.op (k (σ x) X0) (σ (M.op x y))) = X0 ∨ y = (M.op x y) ∨ (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq5857 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5857
  have eq5941 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ (M.op x y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq5856 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5856
  have eq5944 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq5895
       have r₂ := eq609
       grind)
    | exact resolve eq5895 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5895
  have eq5953 : (τ (σ (M.op x y))) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5944 eq116
    | exact resolve eq116 eq5944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq5966 : (M.op x y) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq5953
    | exact resolve eq5953 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5953
  have eq6442 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5854 eq5893
    | exact resolve eq5893 eq5854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5854 eq5893
  have eq6539 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq6442
  have eq7994 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (M.op (σ X0) X2) X2)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq559 (σ X0) (σ X1) X2
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq559
    | (have j0 := eq559 (σ X0) (σ X1) X2
       grind)
    | exact resolve eq559 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8004 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) X0)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq559 y y X0
       have i₂ := eq5966
       grind)
    | exact superpose eq5966 eq559
    | (have j0 := eq559 y y x
       grind)
    | exact resolve eq559 eq5966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq8219 : y = (M.op y y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq175 eq8004
    | exact resolve eq8004 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8004
  have eq8266 : (k y y) = (M.op y y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq182 y
       have i₂ := eq8219
       grind)
    | exact superpose eq8219 eq182
    | exact resolve eq182 eq8219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8294 : y = (k y y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq8219 eq8266
    | exact resolve eq8266 eq8219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8219 eq8266
  have eq8297 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq5966 eq8294
    | exact resolve eq8294 eq5966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5966 eq8294
  have eq8298 : y = (M.op x y) ∨ x = y := by grind
  clear eq8297
  have eq12789 : ∀ X0 : G, (τ X0) = (k y (τ (M.op X0 (M.op (σ (M.op x y)) (σ y))))) ∨ (σ y) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5906 eq108
    | (have j1 := eq5906 X0
       grind)
    | exact resolve eq108 eq5906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq5906
  have eq12799 : ∀ X0 : G, (τ X0) = (k x (τ (M.op X0 (M.op (σ (M.op x y)) (σ y))))) ∨ (σ y) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8298 eq12789
    | (have j0 := eq12789 X0
       grind)
    | exact resolve eq12789 eq8298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12789
  have eq34031 : (τ (σ (M.op x y))) = (k x (τ (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6539 eq12799
    | (have j0 := eq12799 (σ (M.op x y))
       grind)
    | exact resolve eq12799 eq6539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34034 : ∀ X0 : G, (σ (τ X0)) = (k (σ x) (M.op X0 (M.op (σ (M.op x y)) (σ y)))) ∨ (σ y) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12799 eq39
    | (have j1 := eq12799 X0
       grind)
    | exact resolve eq39 eq12799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq12799
  have eq34040 : (τ (σ (M.op x y))) = (k x (τ (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq34031
  have eq34048 : ∀ X0 : G, (σ (τ X0)) = (k (σ x) (M.op X0 (M.op (σ (M.op x y)) (σ y)))) ∨ (σ y) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq34034 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq34034
    | (have j0 := eq34034 X0
       grind)
    | exact resolve eq34034 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34034
  have eq34051 : (τ (σ (M.op x y))) = (k x (τ (σ y))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq34040
       have r₂ := eq609
       grind)
    | exact resolve eq34040 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34040
  have eq34060 : ∀ X0 : G, (k (σ x) (M.op X0 (M.op (σ (M.op x y)) (σ y)))) = X0 ∨ (σ y) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq34048 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq34048
    | (have j0 := eq34048 X0
       grind)
    | exact resolve eq34048 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34048
  have eq34062 : (τ (σ (M.op x y))) = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq34051
    | exact resolve eq34051 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34051
  have eq34070 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq34062
    | exact resolve eq34062 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq34062
  have eq34073 : (M.op x y) = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8298 eq34070
    | exact resolve eq34070 eq8298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8298 eq34070
  have eq34077 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq34073
       grind)
    | exact superpose eq34073 eq40
    | exact resolve eq40 eq34073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34073
  have eq34084 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq34077
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq34077
    | exact resolve eq34077 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34077
  have eq34086 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq34084
    | exact resolve eq34084 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34084
  have eq34092 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34086 eq5940
    | (have j0 := eq5940 (σ x)
       grind)
    | exact resolve eq5940 eq34086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34101 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34086 eq576
    | (have j0 := eq576 (σ x) (σ x)
       grind)
    | exact resolve eq576 eq34086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34104 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq34092
  have eq34154 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq34104 eq182
    | exact resolve eq182 eq34104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34222 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq34086 eq34154
    | exact resolve eq34154 eq34086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34154
  have eq34255 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq34104 eq34222
    | exact resolve eq34222 eq34104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34104 eq34222
  have eq34298 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq34255 eq5932
    | exact resolve eq5932 eq34255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5932
  have eq34339 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq34298
  have eq35018 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6539 eq34060
    | (have j0 := eq34060 (σ (M.op x y))
       grind)
    | exact resolve eq34060 eq6539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6539 eq34060
  have eq35034 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq35018
  have eq35043 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq35034
       have r₂ := eq609
       grind)
    | exact resolve eq35034 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35034
  have eq35053 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35043 eq5940
    | (have j0 := eq5940 (σ y)
       grind)
    | exact resolve eq5940 eq35043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5940
  have eq35064 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35043 eq576
    | (have j0 := eq576 (σ y) (σ x)
       grind)
    | exact resolve eq576 eq35043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq35043
  have eq35070 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq35053
  have eq35091 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq35070 eq34255
    | exact resolve eq34255 eq35070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34255 eq35070
  have eq35150 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq35091
  have eq35175 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq35150
       have r₂ := eq35064
       grind)
    | exact resolve eq35150 eq35064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35064 eq35150
  have eq35200 : (σ x) = (k (M.op (σ x) (M.op (σ x) (σ x))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq35175 eq2774
    | exact resolve eq2774 eq35175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2774
  have eq35236 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq35175 eq5939
    | (have j0 := eq5939 (σ y)
       grind)
    | exact resolve eq5939 eq35175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5939
  have eq35237 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq35175 eq5941
    | exact resolve eq5941 eq35175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5941 eq35175
  have eq35269 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq35237
  have eq35270 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq35236
  have eq35302 : (σ x) = (k (M.op (σ x) (M.op (σ x) (σ x))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq35200
  have eq35316 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq35270
       have r₂ := eq609
       grind)
    | exact resolve eq35270 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35270
  have eq35338 : (σ x) = (k (k (M.op (σ x) (σ x)) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq35302
       have i₂ := eq182 sF2
       grind)
    | exact superpose eq182 eq35302
    | exact resolve eq35302 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35302
  have eq35356 : (σ x) = (k (k (k (σ x) (σ x)) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq28 eq35338
    | (have j1 := eq28 (σ x) (σ x)
       grind)
    | exact resolve eq35338 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35338
  have eq35366 : (σ x) = (k (k (σ (M.op x y)) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq34086 eq35356
    | exact resolve eq35356 eq34086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34086 eq35356
  have eq35372 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq35316 eq35366
    | exact resolve eq35366 eq35316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35316 eq35366
  have eq35373 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5944 eq35372
    | exact resolve eq35372 eq5944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5944 eq35372
  have eq35374 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq35373
       have r₂ := eq34101
       grind)
    | exact resolve eq35373 eq34101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35373
  have eq35554 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq35374 eq34339
    | exact resolve eq34339 eq35374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35374
  have eq35627 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq35554
  have eq35715 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq35627 eq26
    | exact resolve eq26 eq35627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36101 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq603 eq35715
    | exact resolve eq35715 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq35715
  have eq36166 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq35627 eq36101
    | exact resolve eq36101 eq35627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35627 eq36101
  have eq36211 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq36166
       have r₂ := eq34101
       grind)
    | exact resolve eq36166 eq34101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34101 eq36166
  have eq36259 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36211 eq34339
    | exact resolve eq34339 eq36211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34339
  have eq36332 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq36259
  have eq37197 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36332 eq609
    | exact resolve eq609 eq36332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq37310 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36332 eq35269
    | exact resolve eq35269 eq36332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35269 eq36332
  have eq37313 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq37310
  have eq37427 : (σ x) ≠ (σ y) ∨ y = (M.op x y) := by grind
  clear eq37197
  have eq37428 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq36211 eq37313
    | exact resolve eq37313 eq36211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36211 eq37313
  have eq37429 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq37428
  have eq37516 : y = (M.op x y) := by
    first
    | (have r₁ := eq37429
       have r₂ := eq37427
       grind)
    | exact resolve eq37429 eq37427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37427 eq37429
  have eq37582 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq37516
       grind)
    | exact superpose eq37516 eq18
    | exact resolve eq18 eq37516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq37583 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq37516
       grind)
    | exact superpose eq37516 eq24
    | exact resolve eq24 eq37516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq37586 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq37516
       grind)
    | exact superpose eq37516 eq175
    | exact resolve eq175 eq37516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq37589 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 x)) (M.op X1 (M.op (M.op x y) (M.op x y)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq189 X1 X0
       have i₂ := eq37516
       grind)
    | exact superpose eq37516 eq189
    | exact resolve eq189 eq37516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq37592 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq767
       have i₂ := eq37516
       grind)
    | exact superpose eq37516 eq767
    | (have r₁ := eq767
       have r₂ := eq37516
       grind)
    | exact resolve eq767 eq37516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq37593 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op x y) (M.op x y))) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq2124 X0
       have i₂ := eq37516
       grind)
    | exact superpose eq37516 eq2124
    | exact resolve eq2124 eq37516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2124
  have eq37594 : (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq37592
  have eq37596 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq37583 eq20
    | exact resolve eq20 eq37583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37607 : ∀ X0 : G, (τ (k (σ y) X0)) = (k (M.op x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq37583 eq373
    | exact resolve eq373 eq37583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373 eq37583
  have eq37790 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x (M.op (M.op y X0) X0))) := by
    intro X0
    first
    | exact superpose eq37582 eq183
    | exact resolve eq183 eq37582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq37812 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x (M.op (M.op (M.op x y) X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq37790 X0
       have i₂ := eq37516
       grind)
    | exact superpose eq37516 eq37790
    | exact resolve eq37790 eq37516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37790
  have eq38353 : (M.op x y) = (M.op (k (M.op (M.op x y) (M.op x y)) (M.op x y)) x) := by
    first
    | (have i₁ := eq37593 sF0
       have i₂ := eq182 sF0
       grind)
    | exact superpose eq182 eq37593
    | exact resolve eq37593 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37593
  have eq38467 : (k (M.op x y) (τ (σ x))) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq554 eq37607
    | exact resolve eq37607 eq554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37607
  have eq38517 : (k (M.op x y) x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq38467
    | exact resolve eq38467 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38467
  have eq38530 : (M.op x y) = (M.op (k (k (M.op x y) (M.op x y)) (M.op x y)) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq38353
       have i₂ := eq28 sF0 sF0
       grind)
    | exact superpose eq28 eq38353
    | (have j1 := eq28 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq38353 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38353
  have eq39769 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x (M.op x (M.op (M.op (M.op x y) X0) X0)))) := by
    intro X0
    first
    | exact superpose eq37812 eq37586
    | exact resolve eq37586 eq37812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37812
  have eq40239 : ∀ X0 : G, (k (M.op x y) x) ≠ X0 ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq37594 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 (k (M.op x y) x) (M.op x y)
       have r₂ := eq37594
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq37594
       grind)
    | exact resolve eq13 eq37594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40241 : ∀ X0 : G, (M.op x y) = (M.op (k (M.op x y) x) (M.op (M.op (M.op x y) X0) X0)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq37594 eq16
    | exact resolve eq16 eq37594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40243 : (k (M.op x y) x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq37594 eq28
    | exact resolve eq28 eq37594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48172 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op (k (k (M.op x y) (M.op x y)) (M.op x y)) (M.op (M.op x y) (M.op x y)))) = X0 ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq38530 eq37589
    | exact resolve eq37589 eq38530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37589 eq38530
  have eq48203 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op (k (k (M.op x y) (M.op x y)) (M.op x y)) (k (M.op x y) (M.op x y)))) = X0 ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq28 eq48172
    | (have j1 := eq28 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq48172 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq48172
  have eq57026 : ∀ X0 : G, (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op (M.op (M.op x y) X0) X0)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq38517 eq40241
    | exact resolve eq40241 eq38517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57054 : (M.op x y) = (M.op (k (M.op x y) x) (M.op (k (M.op x y) x) (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq37594 eq40241
    | exact resolve eq40241 eq37594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57211 : (M.op x y) = (M.op (k (M.op x y) x) (M.op (k (M.op x y) x) (M.op x y))) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq57054
  have eq57959 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op (τ (M.op (σ x) (σ y))) (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38517 eq57211
    | exact resolve eq57211 eq38517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38517
  have eq57969 : ∀ X0 : G, (k (M.op x y) x) = (M.op (M.op x y) (M.op (M.op (M.op (k (M.op x y) x) (M.op x y)) X0) X0)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq57211 eq16
    | exact resolve eq16 eq57211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57211
  have eq78837 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op (τ (M.op (σ x) (σ y))) (M.op (M.op (M.op x y) X0) X0))) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq57959 eq180
    | exact resolve eq180 eq57959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq57959
  have eq78869 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq57026 eq78837
    | exact resolve eq78837 eq57026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57026 eq78837
  have eq126216 : (M.op x y) = (M.op (k (M.op x y) x) (M.op (k (k (M.op x y) (M.op x y)) (M.op x y)) (k (M.op x y) (M.op x y)))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq40241 (k sF0 sF0)
       have i₂ := eq556 sF0
       grind)
    | exact superpose eq556 eq40241
    | (have j1 := eq556 (M.op x y)
       grind)
    | exact resolve eq40241 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556 eq40241
  have eq126281 : (M.op x y) = (M.op (k (M.op x y) x) (M.op (k (k (M.op x y) (M.op x y)) (M.op x y)) (k (M.op x y) (M.op x y)))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq37594 eq126216
    | exact resolve eq126216 eq37594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126216
  have eq126311 : (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (M.op (k (k (M.op x y) (M.op x y)) (M.op x y)) (k (M.op x y) (M.op x y)))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq40243 eq126281
    | exact resolve eq126281 eq40243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126281
  have eq480307 : (k (M.op x y) x) = (M.op (M.op x y) (M.op (k (M.op x y) x) (M.op (k (k (M.op x y) (M.op x y)) (M.op x y)) (k (M.op x y) (M.op x y))))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq48203 eq57969
    | exact resolve eq57969 eq48203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48203 eq57969
  have eq481215 : (k (M.op x y) x) = (M.op (M.op x y) (M.op (k (M.op x y) x) (M.op (k (k (M.op x y) (M.op x y)) (M.op x y)) (k (M.op x y) (M.op x y))))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq37594 eq480307
    | exact resolve eq480307 eq37594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480307
  have eq481376 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (k (M.op x y) (M.op x y)) (M.op (k (k (M.op x y) (M.op x y)) (M.op x y)) (k (M.op x y) (M.op x y))))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq40243 eq481215
    | exact resolve eq481215 eq40243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40243 eq481215
  have eq481440 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq126311 eq481376
    | exact resolve eq481376 eq126311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126311 eq481376
  have eq481456 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j1 := eq40239 (M.op x y)
       grind)
    | (have r₁ := eq481440
       have r₂ := eq40239 (M.op x y)
       grind)
    | exact resolve eq481440 eq40239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40239 eq481440
  have eq481510 : (k (M.op x y) x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq481456 eq37594
    | exact resolve eq37594 eq481456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37594
  have eq481553 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq481456 eq78869
    | exact resolve eq78869 eq481456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78869 eq481456
  have eq481770 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq481553
  have eq481771 : (k (M.op x y) x) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq481510
  have eq482009 : (k (σ (M.op x y)) (σ x)) = (σ (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq481771 eq40
    | exact resolve eq40 eq481771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq481771
  have eq482086 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq42 eq482009
    | exact resolve eq482009 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq482009
  have eq482112 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq37596 eq482086
    | exact resolve eq482086 eq37596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482086
  have eq482122 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq482112
    | exact resolve eq482112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482112
  have eq482129 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq37596 eq482122
    | exact resolve eq482122 eq37596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482122
  have eq483373 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (τ (M.op (σ x) (σ y)))) (M.op (M.op (σ (M.op x y)) X0) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq481770 eq7994
    | (have j0 := eq7994 (M.op x y) (M.op x y) x
       grind)
    | exact resolve eq7994 eq481770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7994 eq481770
  have eq483386 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (τ (M.op (σ x) (σ y)))) (M.op (M.op (σ (M.op x y)) X0) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq483373
    | (have j0 := eq483373 X0
       grind)
    | exact resolve eq483373 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483373
  have eq483420 : ∀ X0 : G, (σ y) = (M.op (σ (τ (M.op (σ x) (σ y)))) (M.op (M.op (σ y) X0) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq37596 eq483386
    | exact resolve eq483386 eq37596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483386
  have eq483447 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq483420 X0
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq483420
    | exact resolve eq483420 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483420
  have eq483467 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq176 eq483447
    | exact resolve eq483447 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483447
  have eq483475 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq483467
    | exact resolve eq483467 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483467
  have eq483479 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37596 eq483475
    | exact resolve eq483475 eq37596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483475
  have eq486485 : ∀ X0 : G, (σ y) = (M.op (k (σ y) (σ y)) (M.op (M.op (σ y) X0) X0)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq483479 eq546
    | exact resolve eq546 eq483479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq483479
  have eq486579 : ∀ X0 : G, (σ y) = (M.op (k (σ y) (σ x)) (M.op (M.op (σ y) X0) X0)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq482129 eq486485
    | exact resolve eq486485 eq482129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482129 eq486485
  have eq486607 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X0)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq554 eq486579
    | exact resolve eq486579 eq554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq486579
  have eq486629 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq176 eq486607
    | exact resolve eq486607 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq486607
  have eq486630 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq486629
  have eq486718 : (k (M.op x y) x) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq182 x
       have i₂ := eq486630
       grind)
    | exact superpose eq486630 eq182
    | exact resolve eq182 eq486630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486630
  have eq486802 : (M.op x y) = (k (M.op x y) x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37582 eq486718
    | exact resolve eq486718 eq37582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486718
  have eq486985 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq486802 eq774
    | (have j0 := eq774 (M.op x y) x
       grind)
    | exact resolve eq774 eq486802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486802
  have eq486995 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq486985
  have eq487006 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq486995
    | exact resolve eq486995 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486995
  have eq487027 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37596 eq487006
    | exact resolve eq487006 eq37596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487006
  have eq487048 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq487027
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq487027
    | exact resolve eq487027 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487027
  have eq487056 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq487048
    | exact resolve eq487048 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487048
  have eq487057 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq487056
  have eq487062 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq487057 eq27
    | exact resolve eq27 eq487057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487057
  have eq487093 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq487062
       have r₂ := eq37596
       grind)
    | exact resolve eq487062 eq37596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487062
  have eq487094 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq487093 eq26
    | exact resolve eq26 eq487093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq487095 : y = (τ (σ x)) := by
    first
    | exact superpose eq487093 eq32
    | exact resolve eq32 eq487093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq487645 : x = y := by
    first
    | exact superpose eq30 eq487095
    | exact resolve eq487095 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq487095
  have eq487661 : x = (M.op x y) := by
    first
    | (have i₁ := eq487645
       have i₂ := eq37516
       grind)
    | exact superpose eq37516 eq487645
    | exact resolve eq487645 eq37516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37516 eq487645
  have eq487667 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq487661
       grind)
    | exact superpose eq487661 eq22
    | exact resolve eq22 eq487661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq487898 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq37582
       have i₂ := eq487661
       grind)
    | exact superpose eq487661 eq37582
    | exact resolve eq37582 eq487661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37582
  have eq487937 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq39769 X0
       have i₂ := eq487661
       grind)
    | exact superpose eq487661 eq39769
    | exact resolve eq39769 eq487661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39769
  have eq488266 : (M.op x y) = (M.op (M.op x y) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq37586 eq487937
    | exact resolve eq487937 eq37586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37586 eq487937
  have eq488340 : (M.op x y) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq488266
       have i₂ := eq487661
       grind)
    | exact superpose eq487661 eq488266
    | exact resolve eq488266 eq487661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487661 eq488266
  have eq488385 : (M.op x y) = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq488340
       have i₂ := eq182 sF0
       grind)
    | exact superpose eq182 eq488340
    | exact resolve eq488340 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq488340
  have eq488415 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq487898 eq488385
    | exact resolve eq488385 eq487898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487898 eq488385
  have eq502809 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq487667 eq20
    | exact resolve eq20 eq487667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487667
  have eq505310 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq488415 eq774
    | (have j0 := eq774 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq774 eq488415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774 eq488415
  have eq505320 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq505310
  have eq505331 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq505320
    | exact resolve eq505320 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq505320
  have eq505374 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq37596 eq505331
    | exact resolve eq505331 eq37596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37596 eq505331
  have eq505406 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq487093 eq505374
    | exact resolve eq505374 eq487093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487093 eq505374
  have eq505509 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq505406 eq487094
    | exact resolve eq487094 eq505406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487094 eq505406
  have eq505813 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq505509 eq27
    | exact resolve eq27 eq505509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq505509
  have eq505895 : False := by grind
  exact eq505895

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_y_pyx_Equation1662 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 (M.op (M.op X2 X3) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op X0 X2) (M.op (M.op X2 X3) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq71 : y ≠ (M.op x y) ∨ x = y ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq90 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq91 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq94 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq90
  have eq95 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq94
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq89
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq89
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq96
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96
    | exact resolve eq96 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq102
    | exact resolve eq102 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
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
  have eq110 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq91 eq16
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq129 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq95
       grind)
    | exact superpose eq95 eq16
    | exact resolve eq16 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq762 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op x y) y)) x) = X0 := by
    intro X0
    first
    | exact superpose eq53 eq58
    | exact resolve eq58 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq763 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq54 eq58
    | exact resolve eq58 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq903 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq104 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq904 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq903
    | exact resolve eq903 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq907 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq904
       have r₂ := eq28
       grind)
    | exact resolve eq904 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq909 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq907
    | exact resolve eq907 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907
  have eq935 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq909 eq72
    | (have r₁ := eq72
       have r₂ := eq909
       grind)
    | exact resolve eq72 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq909
  have eq939 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq935
  have eq940 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq939
  have eq959 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq940 eq104
    | exact resolve eq104 eq940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq960 : (τ (σ x)) = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq940 eq101
    | exact resolve eq101 eq940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq963 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq959
  have eq967 : x = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq960
    | exact resolve eq960 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq970 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq967
       have r₂ := eq71
       grind)
    | exact resolve eq967 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq967
  have eq973 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq89
       have i₂ := eq970
       grind)
    | exact superpose eq970 eq89
    | exact resolve eq89 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq978 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq973
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq973
    | exact resolve eq973 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq986 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq978 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq987 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq986
  have eq991 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq987
    | exact resolve eq987 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq994 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq991
    | exact resolve eq991 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq998 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq963 eq30
    | exact resolve eq30 eq963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq1019 : x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq998
    | exact resolve eq998 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq1020 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1019
  have eq1024 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1020 eq29
    | exact resolve eq29 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1032 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1020 eq104
    | exact resolve eq104 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq1020
  have eq1039 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1032
  have eq1047 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq1024
    | exact resolve eq1024 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1050 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1047 eq21
    | exact resolve eq21 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1052 : ∀ X0 : G, x = (M.op y (M.op (M.op y X0) X0)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1047 eq53
    | exact resolve eq53 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq1047
  have eq1075 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1050
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1050
    | exact resolve eq1050 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq1149 : (τ (σ (M.op x y))) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1039 eq110
    | exact resolve eq110 eq1039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq1153 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq1149
    | exact resolve eq1149 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149
  have eq1363 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq994 eq28
    | exact resolve eq28 eq994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994
  have eq1469 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1075 eq1363
    | (have r₁ := eq1363
       have r₂ := eq1075
       grind)
    | exact resolve eq1363 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1363
  have eq1470 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1469
  have eq1471 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1470
  have eq1481 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1471 eq763
    | exact resolve eq763 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq1486 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27 eq1481
    | (have j0 := eq1481 X0
       grind)
    | exact resolve eq1481 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1481
  have eq39610 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1471 eq1486
    | exact resolve eq1486 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471 eq1486
  have eq39649 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq39610 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39610
  have eq40467 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3⟩ := hcon
    have f40467_16 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ (σ x) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
      intro X0
      grind
    have f40467_22 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
      intro X0 X1 X2
      grind
    have f40467_25 : X1 ≠ (M.op (M.op X1 X0) X0) := by grind
    have f40467_26 : (σ x) ≠ (σ (M.op x y)) := by grind
    have f40467_27 : x ≠ y := by grind
    have f40467_28 : x ≠ (M.op x y) := by grind
    have f40467_30 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ x = y ∨ x = (M.op x y) := by
      intro X0
      first
      | (have j0 := f40467_16 X0
         grind)
      | (have r₁ := f40467_16 X0
         have r₂ := f40467_26
         grind)
      | exact resolve f40467_16 f40467_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f40467_31 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ x = (M.op x y) := by
      intro X0
      first
      | (have j0 := f40467_30 X0
         grind)
      | (have r₁ := f40467_30 X0
         have r₂ := f40467_27
         grind)
      | exact resolve f40467_30 f40467_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f40467_32 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 := by
      intro X0
      first
      | (have j0 := f40467_31 X0
         grind)
      | (have r₁ := f40467_31 X0
         have r₂ := f40467_28
         grind)
      | exact resolve f40467_31 f40467_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f40467_50 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 := by
      intro X0 X1
      first
      | (have i₁ := f40467_22 X1 X0 (σ x)
         have i₂ := f40467_32 X0
         grind)
      | exact superpose f40467_32 f40467_22
      | exact resolve f40467_22 f40467_32
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f40467_55 : X1 ≠ X1 := by
      first
      | (have i₁ := f40467_25
         have i₂ := f40467_50 X0 X1
         grind)
      | exact superpose f40467_50 f40467_25
      | (have r₁ := f40467_25
         have r₂ := f40467_50 X0 X1
         grind)
      | exact resolve f40467_25 f40467_50
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f40467_58 : False := by grind
    exact f40467_58
  have eq40506 : x = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq39649 eq1052
    | exact resolve eq1052 eq39649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052 eq39649
  have eq40547 : x = (M.op y y) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq40506
  have eq40749 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq95
       have i₂ := eq40547
       grind)
    | exact superpose eq40547 eq95
    | exact resolve eq95 eq40547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq40547
  have eq40829 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq40749
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq40749
    | exact resolve eq40749 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40749
  have eq43289 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq40829 eq40467
    | exact resolve eq40467 eq40829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40467 eq40829
  have eq43514 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq43289
  have eq43622 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq43514
    | exact resolve eq43514 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43514
  have eq43650 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq43622 eq28
    | exact resolve eq28 eq43622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43622
  have eq43719 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq43650
       have r₂ := eq1075
       grind)
    | exact resolve eq43650 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075 eq43650
  have eq43721 : x = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq43719 eq29
    | exact resolve eq29 eq43719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43719
  have eq43950 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq43721
    | exact resolve eq43721 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43721
  have eq43951 : x = (M.op x y) ∨ x = y := by grind
  clear eq43950
  have eq44191 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq43951 eq21
    | exact resolve eq21 eq43951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44256 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) x) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq43951 eq762
    | exact resolve eq762 eq43951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq44260 : x = (k y x) ∨ x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq43951 eq1153
    | exact resolve eq1153 eq43951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153
  have eq44305 : x = (k y x) ∨ x = y := by grind
  clear eq44260
  have eq44312 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) x) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq44256 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq44256
    | (have j0 := eq44256 X0
       grind)
    | exact resolve eq44256 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44256
  have eq44373 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq44191
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq44191
    | exact resolve eq44191 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44191
  have eq44411 : (k y x) = (τ (k (σ y) (σ (M.op x y)))) ∨ x = y := by
    first
    | exact superpose eq44373 eq101
    | exact resolve eq101 eq44373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq44605 : (k y x) = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq110 eq44411
    | exact resolve eq44411 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44411
  have eq44628 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq89
       have i₂ := eq44305
       grind)
    | exact superpose eq44305 eq89
    | exact resolve eq89 eq44305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44305
  have eq44675 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq44628
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq44628
    | exact resolve eq44628 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44628
  have eq44958 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq44373 eq44675
    | exact resolve eq44675 eq44373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44373 eq44675
  have eq45044 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y := by grind
  clear eq44958
  have eq45068 : (τ (σ (M.op x y))) = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq45044 eq110
    | exact resolve eq110 eq45044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq45044
  have eq45120 : (M.op x y) = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq31 eq45068
    | exact resolve eq45068 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq45068
  have eq45690 : ∀ X0 : G, (M.op (M.op X0 x) x) = X0 ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq43951 eq44312
    | exact resolve eq44312 eq43951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44312
  have eq45739 : ∀ X0 : G, (M.op (M.op X0 x) x) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq45690 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45690
  have eq47338 : (M.op x y) = (k y x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq44605 eq45120
    | exact resolve eq45120 eq44605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44605 eq45120
  have eq47356 : (M.op x y) = (k y x) ∨ x = y := by grind
  clear eq47338
  have eq47442 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq89
       have i₂ := eq47356
       grind)
    | exact superpose eq47356 eq89
    | exact resolve eq89 eq47356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq47356
  have eq47501 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq47442
    | exact resolve eq47442 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47442
  have eq47823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq47501 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq47501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47501
  have eq47881 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq47823
    | exact resolve eq47823 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47823
  have eq47890 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq47881
       have r₂ := eq28
       grind)
    | exact resolve eq47881 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47881
  have eq47895 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq47890
    | exact resolve eq47890 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47890
  have eq48980 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 x
       have i₂ := eq45739 X0
       grind)
    | exact superpose eq45739 eq14
    | exact resolve eq14 eq45739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49026 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq45739 sF3
       grind)
    | exact superpose eq45739 eq54
    | exact resolve eq54 eq45739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq45739
  have eq49158 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq47895 eq49026
    | exact resolve eq49026 eq47895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47895 eq49026
  have eq49207 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq49158
  have eq53055 : (τ (σ x)) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq49207 eq129
    | exact resolve eq129 eq49207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq49207
  have eq53119 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq53055
    | exact resolve eq53055 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53055
  have eq53281 : y = (M.op x y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq48980 y y
       have i₂ := eq53119
       grind)
    | exact superpose eq53119 eq48980
    | exact resolve eq48980 eq53119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48980 eq53119
  have eq53282 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq53281
  have eq53289 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq53282
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53282
    | exact resolve eq53282 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53282
  have eq53356 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq53289 eq30
    | exact resolve eq30 eq53289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq53289
  have eq53640 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq53356
    | exact resolve eq53356 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq53356
  have eq53641 : y = (M.op x y) ∨ x = y := by grind
  clear eq53640
  have eq53761 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq53641 eq43951
    | exact resolve eq43951 eq53641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43951 eq53641
  have eq53796 : x = y := by grind
  clear eq53761
  have eq53921 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq53796
       grind)
    | exact superpose eq53796 eq19
    | exact resolve eq19 eq53796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq53922 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq53796
       grind)
    | exact superpose eq53796 eq25
    | exact resolve eq25 eq53796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq53796
  have eq54065 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq53922
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq53922
    | exact resolve eq53922 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq53922
  have eq54094 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq54065 eq27
    | exact resolve eq27 eq54065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq54065
  have eq54393 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq54094 eq70
    | exact resolve eq70 eq54094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq54094
  have eq54446 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq54393
       have i₂ := eq53921
       grind)
    | exact superpose eq53921 eq54393
    | exact resolve eq54393 eq53921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53921 eq54393
  have eq54461 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54446 eq15
    | exact resolve eq15 eq54446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54446
  have eq54539 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq54461
    | exact resolve eq54461 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq54461
  have eq54560 : False := by grind
  exact eq54560

/-- `Equation1687`: `x = (y ◇ x) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_pyy_pyx_Equation1687 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1687 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1687.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq51 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) y)) := by
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
  have eq52 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) (M.op X0 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X0) X1 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 (M.op (M.op X0 X2) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X0) X1 X0
       have i₂ := eq14 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X0) = (k X0 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    grind
  have eq74 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq83 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  clear eq44
  have eq90 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq83
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq91
    | exact resolve eq91 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq97
    | exact resolve eq97 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq113 : x ≠ (M.op x y) ∨ y = (M.op x x) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq143 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq132 eq16
    | exact resolve eq16 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq134 eq16
    | exact resolve eq16 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq163 : (σ (k (k y x) x)) = (k (k (σ y) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq40 (k y x)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq40
    | exact resolve eq40 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq172 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
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
  have eq212 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op y (M.op x y))) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  clear eq39
  have eq388 : ∀ X0 X1 X3 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op (M.op (M.op X1 (M.op X0 X1)) X3) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 (M.op X1 (M.op X0 X1)) (M.op x (M.op X0 X1)) X3
       have i₂ := eq56 X1 x X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 (M.op x X0) X1
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq487 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq464 (M.op X0 X1) X0
       have i₂ := eq464 X0 X1
       grind)
    | exact superpose eq464 eq464
    | exact resolve eq464 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq488 : (M.op (M.op x y) x) = (M.op x x) := by
    first
    | (have i₁ := eq464 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq464
    | (have j0 := eq464 x y
       grind)
    | exact resolve eq464 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq489 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq51 eq464
    | exact resolve eq464 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq52 eq464
    | exact resolve eq464 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq500 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq464 X0 x
       grind)
    | exact superpose eq464 eq14
    | exact resolve eq14 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq464 y x
       grind)
    | exact superpose eq464 eq51
    | exact resolve eq51 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq524 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) (M.op x y)) := by
    first
    | exact superpose eq488 eq464
    | exact resolve eq464 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq538 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0 x
       have i₂ := eq464 X0 x
       grind)
    | exact superpose eq464 eq67
    | exact resolve eq67 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq539 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq538 X0
       have i₂ := eq464 X0 X0
       grind)
    | exact superpose eq464 eq538
    | exact resolve eq538 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq566 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq539 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 (M.op X0 x) x
       grind)
    | exact superpose eq14 eq539
    | exact resolve eq539 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568 : x = (k (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq54 eq539
    | exact resolve eq539 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq580 : x = (k (M.op x x) x) := by
    first
    | exact superpose eq488 eq568
    | exact resolve eq568 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488 eq568
  have eq581 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq566 X0 x
       have i₂ := eq464 X0 x
       grind)
    | exact superpose eq464 eq566
    | exact resolve eq566 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq583 : x = (M.op x (M.op x x)) := by grind
  clear eq580
  have eq584 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    grind
  clear eq581
  have eq762 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq77 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq77 X0 X0
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq772 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq762 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq778 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq772 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq772 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq772 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq772 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq789 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq778 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq778
    | (have j0 := eq778 X0 X1
       grind)
    | exact resolve eq778 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq816 : (M.op y (M.op x y)) = (M.op (M.op x x) (M.op x y)) := by
    first
    | exact superpose eq489 eq524
    | exact resolve eq524 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq892 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq289 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq289
    | (have j0 := eq289 X0 x
       grind)
    | exact resolve eq289 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq921 : (k (k (M.op x y) x) x) = (τ (k (k (σ (M.op x y)) (σ x)) (σ x))) := by
    first
    | exact superpose eq143 eq892
    | exact resolve eq892 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq1040 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op y (M.op x y)) (M.op x x)) := by
    first
    | exact superpose eq816 eq464
    | exact resolve eq464 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq1043 : x = (M.op (M.op y (M.op x y)) (M.op x x)) := by
    first
    | (have i₁ := eq1040
       have i₂ := eq500 x x
       grind)
    | exact superpose eq500 eq1040
    | exact resolve eq1040 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq1064 : (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) = (M.op x (M.op y (M.op x y))) := by
    first
    | exact superpose eq1043 eq464
    | exact resolve eq464 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq1068 : (M.op x y) = (M.op x (M.op y (M.op x y))) := by
    first
    | exact superpose eq212 eq1064
    | exact resolve eq1064 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq1064
  have eq4070 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq334 X0
       have i₂ := eq584 (τ X0)
       grind)
    | exact superpose eq584 eq334
    | exact resolve eq334 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq4071 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4070 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4070
    | exact resolve eq4070 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4070
  have eq4097 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (σ (M.op (τ X0) (τ X0))) X0
       have i₂ := eq4071 X0
       grind)
    | exact superpose eq4071 eq11
    | (have j0 := eq11 (σ (M.op (τ X0) (τ X0))) X0
       grind)
    | exact resolve eq11 eq4071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4071
  have eq4114 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq4097 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4097
  have eq4709 : ∀ X0 : G, (σ x) ≠ (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (k (σ X0) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq172 eq12
    | (have j0 := eq12 (σ X0) (σ x)
       have j1 := eq172 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ x)
       have r₂ := eq172 X0
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq172 x
       grind)
    | exact resolve eq12 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq4723 : ∀ X0 : G, (σ x) ≠ (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (k (σ X0) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4709 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4709
  have eq4726 : ∀ X0 : G, (σ x) ≠ (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (k (σ X0) (σ x)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq4723 X0
       have j1 := eq12 (σ X0) (σ x)
       grind)
    | (have r₁ := eq4723 x
       have r₂ := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq4723 X0
       have r₂ := eq12 (σ X0) (σ x)
       grind)
    | exact resolve eq4723 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4723
  have eq4745 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq40 eq4726
    | (have j0 := eq4726 X0
       grind)
    | exact resolve eq4726 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq4726
  have eq7397 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq388 X0 X1 x
       have i₂ := eq464 (M.op X1 (M.op X0 X1)) x
       grind)
    | exact superpose eq464 eq388
    | exact resolve eq388 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq7398 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7397 X0 X1
       have i₂ := eq56 X1 X1 X0
       grind)
    | exact superpose eq56 eq7397
    | exact resolve eq7397 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq7397
  have eq14077 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14084 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14077
    | exact resolve eq14077 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14077
  have eq14095 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14084
       have r₂ := eq28
       grind)
    | exact resolve eq14084 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14084
  have eq14097 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14095
    | exact resolve eq14095 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14095
  have eq14106 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14097 eq584
    | exact resolve eq584 eq14097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14097
  have eq14134 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14106
    | exact resolve eq14106 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14106
  have eq14135 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14134
  have eq14197 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq584 x
       have i₂ := eq14135
       grind)
    | exact superpose eq14135 eq584
    | exact resolve eq584 eq14135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14135
  have eq14225 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14197
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14197
    | exact resolve eq14197 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14197
  have eq14226 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14225
  have eq14235 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14226 eq28
    | exact resolve eq28 eq14226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14238 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14226 eq114
    | (have r₁ := eq114
       have r₂ := eq14226
       grind)
    | exact resolve eq114 eq14226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq14226
  have eq14251 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq14238
  have eq17151 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14251 eq99
    | exact resolve eq99 eq14251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14251
  have eq17167 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq17151
  have eq19621 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq17167
  have eq19669 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq19621
    | exact resolve eq19621 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19621
  have eq22117 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq19669 eq99
    | exact resolve eq99 eq19669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq19669
  have eq22138 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq22117
  have eq22141 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22138
       have r₂ := eq28
       grind)
    | exact resolve eq22138 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22138
  have eq22201 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22141 eq500
    | exact resolve eq500 eq22141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22326 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22201 eq539
    | exact resolve eq539 eq22201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22201
  have eq22398 : (τ (σ x)) = (k (M.op x y) x) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22326 eq143
    | exact resolve eq143 eq22326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq22326
  have eq22423 : y = (M.op x x) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq22398
    | exact resolve eq22398 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22398
  have eq22435 : x = (M.op x y) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq584 x
       have i₂ := eq22423
       grind)
    | exact superpose eq22423 eq584
    | exact resolve eq584 eq22423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22423
  have eq22465 : x = (M.op x y) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22435
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq22435
    | exact resolve eq22435 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22435
  have eq22466 : x = (k (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq22465
  have eq22476 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22466 eq132
    | exact resolve eq132 eq22466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22485 : x = (M.op x (M.op x y)) ∨ x = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22466 eq11
    | (have j0 := eq11 (M.op x y) x
       grind)
    | exact resolve eq11 eq22466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22491 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22466 eq789
    | (have j0 := eq789 x x
       grind)
    | exact resolve eq789 eq22466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22466
  have eq22493 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq22491
  have eq22495 : (M.op x y) = (M.op x x) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq22485
  have eq22498 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22493
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22493
    | exact resolve eq22493 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22493
  have eq22510 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22476
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22476
    | exact resolve eq22476 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22476
  have eq22512 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22498
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22498
    | exact resolve eq22498 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22498
  have eq22516 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq22512
    | exact resolve eq22512 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22512
  have eq22540 : (τ (k (σ x) (σ x))) = (k (k (M.op x y) x) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22510 eq921
    | exact resolve eq921 eq22510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq22557 : (k x x) = (k (k (M.op x y) x) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50 eq22540
    | exact resolve eq22540 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq22540
  have eq23072 : x = (M.op x (M.op x y)) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq584 x
       have i₂ := eq22495
       grind)
    | exact superpose eq22495 eq584
    | exact resolve eq584 eq22495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22495
  have eq23092 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq23072
  have eq23108 : x ≠ x ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23092 eq12
    | (have j0 := eq12 (M.op x y) x
       grind)
    | (have r₁ := eq12 (M.op x y) x
       have r₂ := eq23092
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq23092
       grind)
    | exact resolve eq12 eq23092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23092
  have eq23123 : (M.op x x) = (k (M.op x y) x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq23108
  have eq23185 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq22516
  have eq28926 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq487 X0 X1
       have i₂ := eq7398 X0 X1
       grind)
    | exact superpose eq7398 eq487
    | exact resolve eq487 eq7398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487 eq7398
  have eq46368 : (k x x) = (k (M.op x x) x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23123 eq22557
    | exact resolve eq22557 eq23123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22557 eq23123
  have eq46414 : (k x x) = (k (M.op x x) x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq46368
  have eq46429 : (k x x) = (M.op x (M.op x x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq46414
  have eq46440 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq46429
       have i₂ := eq583
       grind)
    | exact superpose eq583 eq46429
    | exact resolve eq46429 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46429
  have eq46888 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq500 x x
       have i₂ := eq46440
       grind)
    | exact superpose eq46440 eq500
    | exact resolve eq500 eq46440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46440
  have eq46905 : x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq489 eq46888
    | exact resolve eq46888 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46888
  have eq47800 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq789 x x
       have i₂ := eq46905
       grind)
    | exact superpose eq46905 eq789
    | (have j0 := eq789 x x
       grind)
    | exact resolve eq789 eq46905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789 eq46905
  have eq47801 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by grind
  clear eq47800
  have eq47802 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by grind
  clear eq47801
  have eq47816 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq47802
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq47802
    | exact resolve eq47802 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47802
  have eq90183 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq47816 eq22141
    | exact resolve eq22141 eq47816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22141 eq47816
  have eq90252 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by grind
  clear eq90183
  have eq90305 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have r₁ := eq90252
       have r₂ := eq14235
       grind)
    | exact resolve eq90252 eq14235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14235 eq90252
  have eq96205 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq584 x
       have i₂ := eq90305
       grind)
    | exact superpose eq90305 eq584
    | exact resolve eq584 eq90305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90305
  have eq96250 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq96205
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96205
    | exact resolve eq96205 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96205
  have eq96251 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq96250
  have eq96271 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq96251 eq1068
    | exact resolve eq1068 eq96251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq96279 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq96251 eq51
    | exact resolve eq51 eq96251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq96251
  have eq96320 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq96279
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96279
    | exact resolve eq96279 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96279
  have eq96327 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq489 eq96320
    | exact resolve eq96320 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96320
  have eq96794 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq96271
       grind)
    | exact superpose eq96271 eq90
    | exact resolve eq90 eq96271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq96813 : (k (M.op x y) x) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  have eq96839 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28926 x x
       have i₂ := eq96271
       grind)
    | exact superpose eq96271 eq28926
    | exact resolve eq28926 eq96271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28926 eq96271
  have eq96845 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq96794
  have eq96850 : (M.op x (M.op x y)) = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq489 eq96839
    | exact resolve eq96839 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96839
  have eq96858 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq96845
    | exact resolve eq96845 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96845
  have eq98228 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq96858 eq23185
    | exact resolve eq23185 eq96858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23185 eq96858
  have eq98271 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq98228
  have eq100536 : (k (σ (M.op x y)) (σ x)) = (σ (M.op x (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq96813 eq132
    | exact resolve eq132 eq96813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq96813
  have eq100744 : y = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq96850 eq96327
    | exact resolve eq96327 eq96850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96327 eq96850
  have eq100770 : y = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq100744
  have eq122506 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq100770 eq100536
    | exact resolve eq100536 eq100770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100536 eq100770
  have eq122608 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq122506
  have eq122614 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq122608
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq122608
    | exact resolve eq122608 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122608
  have eq122647 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122614 eq22510
    | exact resolve eq22510 eq122614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22510 eq122614
  have eq122700 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq122647
  have eq122728 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122700 eq27
    | exact resolve eq27 eq122700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122700
  have eq123492 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122728 eq98271
    | exact resolve eq98271 eq122728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98271 eq122728
  have eq123543 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq123492
  have eq123617 : x = (M.op x y) := by
    first
    | (have r₁ := eq123543
       have r₂ := eq28
       grind)
    | exact resolve eq123543 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123543
  have eq124435 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq123617 eq21
    | exact resolve eq21 eq123617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq124444 : x ≠ x ∨ y = (M.op x x) ∨ (k y x) = (M.op x x) := by
    first
    | exact superpose eq123617 eq113
    | (have r₁ := eq113
       have r₂ := eq123617
       grind)
    | exact resolve eq113 eq123617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq124492 : (M.op x x) = (M.op y x) := by
    first
    | exact superpose eq123617 eq489
    | exact resolve eq489 eq123617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq124493 : y = (M.op x (M.op y y)) := by
    first
    | exact superpose eq123617 eq508
    | exact resolve eq508 eq123617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq124604 : (k y x) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq124444
  have eq124734 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq124435
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq124435
    | exact resolve eq124435 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124435
  have eq124738 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq124734 eq27
    | exact resolve eq27 eq124734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq125221 : (M.op y y) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq464 y x
       have i₂ := eq124492
       grind)
    | exact superpose eq124492 eq464
    | exact resolve eq464 eq124492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464 eq124492
  have eq153830 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq29 eq4114
    | exact resolve eq4114 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4114
  have eq153878 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x x))) ∨ (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq124734 eq153830
    | exact resolve eq153830 eq124734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153830
  have eq153970 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x x))) ∨ (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq124734 eq153878
    | exact resolve eq153878 eq124734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153878
  have eq154154 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) ≠ (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq124734 eq4745
    | (have j0 := eq4745 X0
       grind)
    | exact resolve eq4745 eq124734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4745
  have eq154155 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k X0 x)) ∨ (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq124734 eq154154
    | (have j0 := eq154154 X0
       grind)
    | exact resolve eq154154 eq124734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154154
  have eq154156 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k X0 x)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq124734 eq154155
    | (have j0 := eq154155 X0
       grind)
    | exact resolve eq154155 eq124734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154155
  have eq154186 : (σ (M.op x y)) ≠ (σ (M.op x (M.op x x))) ∨ (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op x (M.op x x))) := by grind
  have eq154203 : ∀ X0 : G, (σ (M.op x y)) ≠ (k X0 (σ x)) ∨ (σ (τ X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq154156 (τ X0)
       have i₂ := eq35 X0 x
       grind)
    | exact superpose eq35 eq154156
    | (have j0 := eq154156 (τ X0)
       grind)
    | exact resolve eq154156 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq154156
  have eq154276 : ∀ X0 : G, (σ (M.op x y)) ≠ (k X0 (σ x)) ∨ (σ (τ X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq154203 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq154203
    | (have j0 := eq154203 X0
       grind)
    | exact resolve eq154203 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154203
  have eq154287 : (σ x) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq154186
       have i₂ := eq583
       grind)
    | exact superpose eq583 eq154186
    | exact resolve eq154186 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154186
  have eq154330 : ∀ X0 : G, (σ (M.op x y)) ≠ (k X0 (σ (M.op x y))) ∨ (σ (τ X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq124734 eq154276
    | (have j0 := eq154276 X0
       grind)
    | exact resolve eq154276 eq124734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154276
  have eq154338 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq154287
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq154287
    | exact resolve eq154287 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154287
  have eq154378 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) ≠ (k X0 (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq154330 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq154330
    | (have j0 := eq154330 X0
       grind)
    | exact resolve eq154330 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154330
  have eq154384 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op x (M.op x x))) := by
    first
    | (have r₁ := eq154338
       have r₂ := eq124734
       grind)
    | exact resolve eq154338 eq124734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154338
  have eq154406 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (k X0 (σ x)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) ≠ (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq154378 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq154378
    | (have j0 := eq154378 X0
       grind)
    | exact resolve eq154378 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154378
  have eq154411 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq154384
       have i₂ := eq583
       grind)
    | exact superpose eq583 eq154384
    | exact resolve eq154384 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154384
  have eq154419 : ∀ X0 : G, (σ (M.op x y)) ≠ (k X0 (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = X0 ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq124734 eq154406
    | (have j0 := eq154406 X0
       grind)
    | exact resolve eq154406 eq124734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154406
  have eq154421 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq154411
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq154411
    | exact resolve eq154411 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154411
  have eq154429 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq124734 eq154421
    | exact resolve eq154421 eq124734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154421
  have eq172202 : (k (k (σ y) (σ x)) (σ x)) = (σ (k (M.op x x) x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq163
       have i₂ := eq124604
       grind)
    | exact superpose eq124604 eq163
    | exact resolve eq163 eq124604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq124604
  have eq172256 : (k (k (σ y) (σ x)) (σ x)) = (σ (M.op x (M.op x x))) ∨ y = (M.op x x) := by grind
  clear eq172202
  have eq172276 : (σ x) = (k (k (σ y) (σ x)) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq172256
       have i₂ := eq583
       grind)
    | exact superpose eq583 eq172256
    | exact resolve eq172256 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583 eq172256
  have eq172294 : (σ x) = (k (k (σ y) (σ (M.op x y))) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq124734 eq172276
    | exact resolve eq172276 eq124734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172276
  have eq172308 : (σ x) = (k (k (σ y) (σ (M.op x y))) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq172294
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq172294
    | exact resolve eq172294 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172294
  have eq172319 : (σ (M.op x y)) = (k (k (σ y) (σ (M.op x y))) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq124734 eq172308
    | exact resolve eq172308 eq124734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172308
  have eq172395 : (σ (M.op x y)) = (k (M.op (σ (M.op x y)) (σ y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq172319
       have i₂ := eq11 sF3 sF1
       grind)
    | exact superpose eq11 eq172319
    | (have j1 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq172319 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172319
  have eq172412 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq124738 eq172395
    | exact resolve eq172395 eq124738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172395
  have eq172414 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq124738 eq172412
    | exact resolve eq172412 eq124738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172412
  have eq172416 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq172414
       have r₂ := eq28
       grind)
    | exact resolve eq172414 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172414
  have eq175094 : (M.op x x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq154429
       grind)
    | exact superpose eq154429 eq16
    | exact resolve eq16 eq154429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154429
  have eq455935 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq172416 eq584
    | exact resolve eq584 eq172416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172416
  have eq456001 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq124738 eq455935
    | exact resolve eq455935 eq124738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455935
  have eq456017 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq456001
       have r₂ := eq28
       grind)
    | exact resolve eq456001 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456001
  have eq676367 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq456017 eq154419
    | (have j0 := eq154419 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq154419 (M.op (σ x) (σ y))
       have r₂ := eq456017
       grind)
    | exact resolve eq154419 eq456017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154419 eq456017
  have eq676385 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) := by grind
  clear eq676367
  have eq680928 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq676385 eq500
    | exact resolve eq500 eq676385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500 eq676385
  have eq680977 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq491 eq680928
    | exact resolve eq680928 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680928
  have eq683735 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq680977 eq52
    | exact resolve eq52 eq680977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq683796 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq124738 eq683735
    | exact resolve eq683735 eq124738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683735
  have eq683805 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq491 eq683796
    | exact resolve eq683796 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491 eq683796
  have eq683955 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq683805 eq680977
    | exact resolve eq680977 eq683805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680977 eq683805
  have eq683987 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq683955
  have eq684052 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq683987 eq539
    | exact resolve eq539 eq683987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539 eq683987
  have eq686573 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq684052 eq157
    | exact resolve eq157 eq684052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq684052
  have eq686812 : (τ (σ (M.op x y))) = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq123617 eq686573
    | exact resolve eq686573 eq123617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686573
  have eq686824 : (M.op x y) = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq686812
    | exact resolve eq686812 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686812
  have eq686832 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x x) := by
    first
    | exact superpose eq123617 eq686824
    | exact resolve eq686824 eq123617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686824
  have eq686863 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq153970
       have i₂ := eq686832
       grind)
    | exact superpose eq686832 eq153970
    | exact resolve eq153970 eq686832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153970 eq686832
  have eq686972 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq686863
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq686863
    | exact resolve eq686863 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686863
  have eq687012 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x x) := by
    first
    | exact superpose eq124738 eq686972
    | exact resolve eq686972 eq124738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686972
  have eq687036 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x x) := by
    first
    | (have r₁ := eq687012
       have r₂ := eq28
       grind)
    | exact resolve eq687012 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687012
  have eq687051 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq687036
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq687036
    | exact resolve eq687036 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687036
  have eq691184 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x x) := by
    first
    | exact superpose eq687051 eq584
    | exact resolve eq584 eq687051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq687051
  have eq691268 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k x x) := by
    first
    | exact superpose eq124738 eq691184
    | exact resolve eq691184 eq124738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691184
  have eq691284 : x = (k x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq691268
       have r₂ := eq28
       grind)
    | exact resolve eq691268 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691268
  have eq693861 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq691284
       grind)
    | exact superpose eq691284 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq691284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691284
  have eq693948 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq693861
  have eq694410 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq125221
       have i₂ := eq693948
       grind)
    | exact superpose eq693948 eq125221
    | exact resolve eq125221 eq693948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125221
  have eq694495 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq694410
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq694410
    | exact resolve eq694410 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694410
  have eq694516 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq123617 eq694495
    | exact resolve eq694495 eq123617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694495
  have eq701889 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq124493
       have i₂ := eq694516
       grind)
    | exact superpose eq694516 eq124493
    | exact resolve eq124493 eq694516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124493 eq694516
  have eq704478 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq693948
       have i₂ := eq701889
       grind)
    | exact superpose eq701889 eq693948
    | exact resolve eq693948 eq701889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693948 eq701889
  have eq704539 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq704478
  have eq706957 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq704539 eq30
    | exact resolve eq30 eq704539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq704539
  have eq707376 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq706957
    | exact resolve eq706957 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq706957
  have eq707443 : x = y ∨ x = y := by
    first
    | exact superpose eq123617 eq707376
    | exact resolve eq707376 eq123617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707376
  have eq707444 : x = y := by grind
  clear eq707443
  have eq707449 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq707444
       grind)
    | exact superpose eq707444 eq19
    | exact resolve eq19 eq707444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq707450 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq707444
       grind)
    | exact superpose eq707444 eq25
    | exact resolve eq25 eq707444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq707444
  have eq707897 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq707450
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq707450
    | exact resolve eq707450 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707450
  have eq707898 : x = (M.op x x) := by
    first
    | exact superpose eq123617 eq707449
    | exact resolve eq707449 eq123617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123617 eq707449
  have eq708028 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq124734 eq707897
    | exact resolve eq707897 eq124734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707897
  have eq708373 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq708028 eq124738
    | exact resolve eq124738 eq708028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124738 eq708028
  have eq708788 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq708373 eq175094
    | exact resolve eq175094 eq708373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175094 eq708373
  have eq708888 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq708788
       have r₂ := eq28
       grind)
    | exact resolve eq708788 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708788
  have eq708898 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq708888
       have i₂ := eq707898
       grind)
    | exact superpose eq707898 eq708888
    | exact resolve eq708888 eq707898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707898 eq708888
  have eq708913 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq708898 eq15
    | exact resolve eq15 eq708898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708898
  have eq709579 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq708913
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq708913
    | exact resolve eq708913 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq708913
  have eq709761 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq124734 eq709579
    | exact resolve eq709579 eq124734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124734 eq709579
  have eq709841 : False := by grind
  exact eq709841

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pxy_pyx_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq37
    | exact resolve eq37 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq37
  have eq84 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq94 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq531 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq94 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq94 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq94 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq94 X0 X0
       grind)
    | exact resolve eq12 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq94 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq13
    | (have j1 := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq94 X0 X1
       grind)
    | exact resolve eq13 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq546 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq532 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq550 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq546 X0 X1
       have j1 := eq84 X1 (σ X0)
       grind)
    | (have r₁ := eq546 X0 X0
       have r₂ := eq84 X0 (σ X0)
       grind)
    | exact resolve eq546 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq551 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq531 X0 X1
       have j1 := eq84 X1 (σ X0)
       grind)
    | (have r₁ := eq531 X0 X0
       have r₂ := eq84 X0 (σ X0)
       grind)
    | exact resolve eq531 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq531
  have eq562 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq550 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq550
    | (have j0 := eq550 X0 X1
       grind)
    | exact resolve eq550 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq563 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq562 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq564 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq551 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq551
    | (have j0 := eq551 X0 X1
       grind)
    | exact resolve eq551 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq572 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq563 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq563
    | (have j0 := eq563 X0 X1
       grind)
    | exact resolve eq563 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq563
  have eq573 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq564 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq564
    | (have j0 := eq564 X0 X1
       grind)
    | exact resolve eq564 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq574 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq573 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq580 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq574 X0 X1
       have j1 := eq572 X0 X1
       grind)
    | (have r₁ := eq574 X0 X1
       have r₂ := eq572 X0 X1
       grind)
    | exact resolve eq574 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq574
  have eq582 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq580 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq580
    | exact resolve eq580 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq580 x y
       grind)
    | exact superpose eq580 eq16
    | exact resolve eq16 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq687 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq582 X0 (τ X1)
       grind)
    | exact superpose eq582 eq18
    | exact resolve eq18 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq582
  have eq720 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq687 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq687
    | exact resolve eq687 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq737 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq720 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq720
    | exact resolve eq720 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq795 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq593
       have i₂ := eq737 x y
       grind)
    | exact superpose eq737 eq593
    | exact resolve eq593 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593 eq737
  have eq796 : False := by grind
  exact eq796

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq89 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq412 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq89 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq89 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq89 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq13 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq89 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq435 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq412 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq436 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq435 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq438 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq436 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq436
    | (have j0 := eq436 X0 X1
       grind)
    | exact resolve eq436 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq441 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq438 X0 X1
       have j1 := eq432 X1 X0
       grind)
    | (have r₁ := eq438 X1 X0
       have r₂ := eq432 X0 X1
       grind)
    | (have r₁ := eq438 X1 (k X0 X1)
       have r₂ := eq432 X0 X1
       grind)
    | (have r₁ := eq438 X1 X1
       have r₂ := eq432 X1 X1
       grind)
    | exact resolve eq438 eq432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432 eq438
  have eq599 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq441 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq441
    | exact resolve eq441 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq607 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq441 y x
       grind)
    | exact superpose eq441 eq16
    | (have j1 := eq441 y x
       grind)
    | exact resolve eq16 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq626 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq599 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq599
    | (have j0 := eq599 X0 X1
       grind)
    | exact resolve eq599 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq599
  have eq633 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq626 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq626
    | exact resolve eq626 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq732 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq633 (τ X0) X1
       grind)
    | exact superpose eq633 eq18
    | (have j1 := eq633 (τ X0) X1
       grind)
    | exact resolve eq18 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq633
  have eq934 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq732 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq732
    | exact resolve eq732 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq985 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq934 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq934
    | (have j0 := eq934 X0 X1
       grind)
    | exact resolve eq934 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq1102 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq607
       have i₂ := eq985 x y
       grind)
    | exact superpose eq985 eq607
    | (have j1 := eq985 (σ x) (σ y)
       grind)
    | (have r₁ := eq607
       have r₂ := eq985 x y
       grind)
    | exact resolve eq607 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1103 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1102
  have eq1115 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1103
  have eq1128 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq607
       have i₂ := eq1115
       grind)
    | exact superpose eq1115 eq607
    | exact resolve eq607 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607 eq1115
  have eq1129 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1128
  have eq1130 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1129
  have eq1167 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1130
  have eq1182 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1167
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1167
    | exact resolve eq1167 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq1187 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1182
       grind)
    | exact superpose eq1182 eq16
    | exact resolve eq16 eq1182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq1247 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1187
       have i₂ := eq985 x y
       grind)
    | exact superpose eq985 eq1187
    | (have j1 := eq985 x y
       grind)
    | (have r₁ := eq1187
       have r₂ := eq985 x y
       grind)
    | exact resolve eq1187 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq1248 : x = (M.op y y) := by grind
  clear eq1247
  have eq1253 : (M.op x y) = (k x y) := by grind
  clear eq1248
  have eq1301 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1187
       have i₂ := eq1253
       grind)
    | exact superpose eq1253 eq1187
    | exact resolve eq1187 eq1253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187 eq1253
  have eq1304 : False := by grind
  exact eq1304

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxy_pyx_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X2 X0) X0)) = X0 := by
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
  have eq51 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 y) y)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq84 : (k (σ x) (σ (M.op x y))) = (σ (M.op x (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11 x sF0
       grind)
    | exact superpose eq11 eq46
    | (have j1 := eq11 x (M.op x y)
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq83
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq83
    | exact resolve eq83 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq91
    | exact resolve eq91 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq709 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq76 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq710 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq709 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq20170 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq92 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20178 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq20170
    | exact resolve eq20170 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20170
  have eq20189 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq20178
       have r₂ := eq28
       grind)
    | exact resolve eq20178 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20178
  have eq20191 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20189 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq20189
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq20189
       grind)
    | exact resolve eq12 eq20189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20189
  have eq20209 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq20191
  have eq20210 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq20209
  have eq20216 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20210 eq92
    | exact resolve eq92 eq20210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20210
  have eq20233 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq20216
  have eq20249 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq20233
  have eq20283 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq20249
    | exact resolve eq20249 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20249
  have eq20300 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20283 eq92
    | exact resolve eq92 eq20283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq20283
  have eq20317 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq20300
  have eq20320 : y = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq20317
       have r₂ := eq28
       grind)
    | exact resolve eq20317 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20317
  have eq20323 : ∀ X0 : G, x = (M.op y (M.op (M.op X0 x) x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq20320
       grind)
    | exact superpose eq20320 eq14
    | exact resolve eq14 eq20320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20451 : x = (M.op y (M.op y x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq20323 y
       have i₂ := eq20320
       grind)
    | exact superpose eq20320 eq20323
    | exact resolve eq20323 eq20320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20323
  have eq20474 : x = (M.op y (M.op y x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq20451
  have eq20476 : x = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq20474
       have i₂ := eq20320
       grind)
    | exact superpose eq20320 eq20474
    | exact resolve eq20474 eq20320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20320 eq20474
  have eq20495 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq20476
  have eq20500 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq20495
  have eq20534 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq20500
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20500
    | exact resolve eq20500 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20500
  have eq20547 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq20534
       grind)
    | exact superpose eq20534 eq45
    | exact resolve eq45 eq20534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq20534
  have eq20582 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq20547
    | exact resolve eq20547 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20547
  have eq20944 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20582 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq20582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20958 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq20944
    | exact resolve eq20944 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20944
  have eq20969 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq20958
       have r₂ := eq28
       grind)
    | exact resolve eq20958 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20958
  have eq22960 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20969 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq20969
       grind)
    | exact resolve eq12 eq20969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20969
  have eq22978 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq22960
  have eq22979 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq22978
  have eq23001 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq22979 eq20582
    | exact resolve eq20582 eq22979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22979
  have eq23012 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq23001
  have eq23038 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq23012
  have eq23072 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq23038
    | exact resolve eq23038 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23038
  have eq23107 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq23072 eq20582
    | exact resolve eq20582 eq23072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20582 eq23072
  have eq23118 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq23107
  have eq23129 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq23118
       have r₂ := eq28
       grind)
    | exact resolve eq23118 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23118
  have eq23256 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq23129 eq27
    | exact resolve eq27 eq23129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23257 : y = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq23129 eq30
    | exact resolve eq30 eq23129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq23397 : y = (M.op x y) := by
    first
    | exact superpose eq31 eq23257
    | exact resolve eq23257 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq23257
  have eq24075 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq23397 eq84
    | exact resolve eq84 eq23397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq24076 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq24075
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24075
    | exact resolve eq24075 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24075
  have eq24077 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq21 eq24076
    | exact resolve eq24076 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq24076
  have eq24078 : y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq23397 eq24077
    | exact resolve eq24077 eq23397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24077
  have eq24079 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23397 eq24078
    | exact resolve eq24078 eq23397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24078
  have eq24090 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq24079 eq11
    | (have j0 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq24079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24099 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23256 eq24090
    | exact resolve eq24090 eq23256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24090
  have eq24110 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq24099
       have r₂ := eq28
       grind)
    | exact resolve eq24099 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24099
  have eq102269 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq24110
  have eq102303 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23256 eq102269
    | exact resolve eq102269 eq23256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102269
  have eq111374 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq102303 eq24079
    | exact resolve eq24079 eq102303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102303
  have eq111396 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by grind
  clear eq111374
  have eq111399 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq111396
       have r₂ := eq28
       grind)
    | exact resolve eq111396 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111396
  have eq111415 : ∀ X0 : G, (σ x) = (M.op (σ (M.op x y)) (M.op (M.op X0 (σ x)) (σ x))) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq111399 eq14
    | exact resolve eq14 eq111399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111437 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ x))) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq111399 eq111415
    | exact resolve eq111415 eq111399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111415
  have eq111463 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ x))) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq111437
  have eq111467 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq111399 eq111463
    | exact resolve eq111463 eq111399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111399 eq111463
  have eq111486 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq111467
  have eq111517 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq111486
  have eq111551 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq23256 eq111517
    | exact resolve eq111517 eq23256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23256 eq111517
  have eq111598 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq111551 eq24079
    | exact resolve eq24079 eq111551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24079 eq111551
  have eq111619 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq111598
  have eq111621 : y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq111619
       have r₂ := eq28
       grind)
    | exact resolve eq111619 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111619
  have eq111643 : ∀ X0 : G, x = (M.op y (M.op (M.op X0 x) x)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq111621
       grind)
    | exact superpose eq111621 eq14
    | exact resolve eq14 eq111621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111882 : x = (M.op y (M.op y x)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq111643 y
       have i₂ := eq111621
       grind)
    | exact superpose eq111621 eq111643
    | exact resolve eq111643 eq111621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111643
  have eq111907 : x = (M.op y (M.op y x)) ∨ x = (M.op y y) := by grind
  clear eq111882
  have eq111910 : x = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq111907
       have i₂ := eq111621
       grind)
    | exact superpose eq111621 eq111907
    | exact resolve eq111907 eq111621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111621 eq111907
  have eq111931 : x = (M.op y y) := by grind
  clear eq111910
  have eq111957 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq111931
       grind)
    | exact superpose eq111931 eq51
    | exact resolve eq51 eq111931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq111965 : (M.op x y) = (k x y) := by grind
  have eq112001 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq111965
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq111965
    | exact resolve eq111965 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111965
  have eq112006 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq111957
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq111957
    | exact resolve eq111957 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq111957
  have eq112044 : y = (k x y) := by
    first
    | exact superpose eq23397 eq112001
    | exact resolve eq112001 eq23397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112001
  have eq112049 : y = (M.op y y) := by
    first
    | exact superpose eq23397 eq112006
    | exact resolve eq112006 eq23397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23397 eq112006
  have eq112065 : x = y := by
    first
    | (have i₁ := eq112049
       have i₂ := eq111931
       grind)
    | exact superpose eq111931 eq112049
    | exact resolve eq112049 eq111931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111931 eq112049
  have eq112092 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq112065
       grind)
    | exact superpose eq112065 eq25
    | exact resolve eq25 eq112065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq112440 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq23129 eq112092
    | exact resolve eq112092 eq23129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112092
  have eq112515 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq112440
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq112440
    | exact resolve eq112440 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112440
  have eq112524 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq112515 eq27
    | exact resolve eq27 eq112515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq112750 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq23129 eq112524
    | exact resolve eq112524 eq23129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23129 eq112524
  have eq112828 : x = (k x x) := by
    first
    | (have i₁ := eq112044
       have i₂ := eq112065
       grind)
    | exact superpose eq112065 eq112044
    | exact resolve eq112044 eq112065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112044 eq112065
  have eq112919 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq710 x
       have i₂ := eq112828
       grind)
    | exact superpose eq112828 eq710
    | (have j0 := eq710 x
       grind)
    | exact resolve eq710 eq112828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710 eq112828
  have eq112935 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq112919
  have eq112946 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq112935
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq112935
    | exact resolve eq112935 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq112935
  have eq112967 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq112515 eq112946
    | exact resolve eq112946 eq112515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112515 eq112946
  have eq118216 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq112967 eq112750
    | exact resolve eq112750 eq112967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112750 eq112967
  have eq118217 : False := by grind
  exact eq118217

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxx_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X2 X0) X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq30 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq15
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq86 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq133 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (k X1 (τ X0))
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq61
    | exact resolve eq61 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq145 : ∀ X0 X1 X2 X3 : G, (σ (k (k X0 (τ X1)) (k X2 (τ X3)))) = (k (k (σ X0) X1) (k (σ X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30 X2 X3 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq30
    | exact resolve eq30 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq30
  have eq284 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq84 x y
       grind)
    | exact superpose eq84 eq16
    | (have j1 := eq84 x y
       grind)
    | exact resolve eq16 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq576 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq86 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq86
    | exact resolve eq86 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq618 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq576 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq576
    | (have j0 := eq576 X0 X1
       grind)
    | exact resolve eq576 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq1043 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq284
       have i₂ := eq618 x y
       grind)
    | exact superpose eq618 eq284
    | (have j1 := eq618 (σ x) (σ y)
       grind)
    | (have r₁ := eq284
       have r₂ := eq618 x y
       grind)
    | (have r₁ := eq284
       have r₂ := eq618 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq284
       have r₂ := eq618 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq284 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284 eq618
  have eq1044 : x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq1043
  have eq2318 : ∀ X0 X1 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (k (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    grind
  clear eq133
  have eq2343 : ∀ X0 X1 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (k (k (σ X0) X1) (k (σ X0) X1)) ∨ (M.op (k (σ X0) X1) (k (σ X0) X1)) = (k (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2318 X0 X1
       have i₂ := eq145 X0 X1 X0 X1
       grind)
    | exact superpose eq145 eq2318
    | (have j0 := eq2318 X0 X1
       grind)
    | exact resolve eq2318 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq2318
  have eq2344 : ∀ X0 X1 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (k (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2343 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2343
  have eq2394 : ∀ X0 X1 : G, (k (k X0 X1) (k X0 X1)) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2344 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2344
    | exact resolve eq2344 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2344
  have eq2467 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (k (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  have eq2514 : ∀ X0 : G, (k (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2467 X0
       have i₂ := eq9 X0 (M.op X0 X0) X0
       grind)
    | exact superpose eq9 eq2467
    | exact resolve eq2467 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2467
  have eq2638 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2394 (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)
       have i₂ := eq2514 X0
       grind)
    | exact superpose eq2514 eq2394
    | exact resolve eq2394 eq2514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2394 eq2514
  have eq2681 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2638 (σ X0)
       grind)
    | exact superpose eq2638 eq15
    | exact resolve eq15 eq2638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2705 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2681 X0
       have i₂ := eq2638 X0
       grind)
    | exact superpose eq2638 eq2681
    | exact resolve eq2681 eq2638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2638 eq2681
  have eq3009 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq3041 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3009 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq3009
    | exact resolve eq3009 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3009
  have eq3066 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq3041
  have eq31493 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1044
       grind)
    | exact superpose eq1044 eq16
    | exact resolve eq16 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq31494 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq31493
       have r₂ := eq2705 x
       grind)
    | exact resolve eq31493 eq2705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31493
  have eq31495 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq31494
       have i₂ := eq2705 y
       grind)
    | exact superpose eq2705 eq31494
    | exact resolve eq31494 eq2705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31494
  have eq31497 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq31495
       grind)
    | exact superpose eq31495 eq10
    | exact resolve eq10 eq31495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31495
  have eq31622 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq31497
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq31497
    | exact resolve eq31497 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31497
  have eq32133 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31622
       grind)
    | exact superpose eq31622 eq16
    | exact resolve eq16 eq31622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31622
  have eq32134 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq32133
       have r₂ := eq2705 x
       grind)
    | exact resolve eq32133 eq2705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2705 eq32133
  have eq32164 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3066 y
       have i₂ := eq32134
       grind)
    | exact superpose eq32134 eq3066
    | exact resolve eq3066 eq32134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32134
  have eq32220 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq32164
       have r₂ := eq16
       grind)
    | exact resolve eq32164 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32164
  have eq32609 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq32220
       grind)
    | exact superpose eq32220 eq10
    | exact resolve eq10 eq32220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32220
  have eq32738 : x = (M.op y y) := by
    first
    | (have i₁ := eq32609
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq32609
    | exact resolve eq32609 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32609
  have eq32823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3066 y
       have i₂ := eq32738
       grind)
    | exact superpose eq32738 eq3066
    | exact resolve eq3066 eq32738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3066 eq32738
  have eq32880 : False := by grind
  exact eq32880

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq24
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
  have eq63 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq57 (τ X0)
       grind)
    | exact superpose eq57 eq18
    | exact resolve eq18 eq57
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
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq60
    | exact resolve eq60 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq72 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq66
    | exact resolve eq66 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq66
  have eq83 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq95 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq69 X1
       grind)
    | exact superpose eq69 eq95
    | (have j0 := eq95 X0 X1
       grind)
    | exact resolve eq95 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq427 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq97 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq97
    | (have j0 := eq97 X0 X1
       grind)
    | exact resolve eq97 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq457 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq427 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq427
    | (have j0 := eq427 X0 X1
       grind)
    | exact resolve eq427 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq427
  have eq461 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq457 X0 X1
       have j1 := eq84 X1 X0
       grind)
    | (have r₁ := eq457 X0 X0
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq457 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq465 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq461 X0 X1
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq461
    | (have j0 := eq461 X0 X1
       grind)
    | exact resolve eq461 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq671 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq465 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq465
    | exact resolve eq465 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq683 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq465 (σ X0) X1
       grind)
    | exact superpose eq465 eq15
    | (have j1 := eq465 (σ X0) X1
       grind)
    | exact resolve eq15 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq702 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq683 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq683
    | (have j0 := eq683 X0 X1
       grind)
    | exact resolve eq683 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq720 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq671 (τ X1) X0
       grind)
    | exact superpose eq671 eq18
    | (have j1 := eq671 (τ X1) X0
       grind)
    | exact resolve eq18 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq671
  have eq1227 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq720 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq720
    | exact resolve eq720 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq1275 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1227 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1227
    | (have j0 := eq1227 X0 X1
       grind)
    | exact resolve eq1227 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq5293 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq702 x y
       grind)
    | exact superpose eq702 eq16
    | (have j1 := eq702 x y
       grind)
    | exact resolve eq16 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5342 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq702 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq5385 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq5293
       have i₂ := eq1275 y x
       grind)
    | exact superpose eq1275 eq5293
    | (have j1 := eq1275 y x
       grind)
    | (have r₁ := eq5293
       have r₂ := eq1275 y x
       grind)
    | exact resolve eq5293 eq1275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5293
  have eq5386 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq5385
  have eq5468 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ y = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq5386
       grind)
    | exact superpose eq5386 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq5386
       grind)
    | exact resolve eq13 eq5386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5386
  have eq5487 : (k x y) = (M.op x x) ∨ y = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq5468
  have eq5499 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5342 (τ X0) (τ X1)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq5342
    | (have j0 := eq5342 (τ X0) (τ X1)
       grind)
    | exact resolve eq5342 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq5557 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5499 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq5499
    | (have j0 := eq5499 X0 X1
       grind)
    | exact resolve eq5499 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5499
  have eq5584 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5557 X0 X1
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq5557
    | (have j0 := eq5557 X0 X1
       grind)
    | exact resolve eq5557 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5557
  have eq5602 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5584 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5584
    | (have j0 := eq5584 X0 X1
       grind)
    | exact resolve eq5584 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5584
  have eq5612 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5602 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5602
    | (have j0 := eq5602 X0 X1
       grind)
    | exact resolve eq5602 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5602
  have eq5617 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5612 X0 X1
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq5612
    | (have j0 := eq5612 X0 X1
       grind)
    | exact resolve eq5612 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq5612
  have eq17395 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5342 x y
       have i₂ := eq5487
       grind)
    | exact superpose eq5487 eq5342
    | (have j0 := eq5342 x y
       grind)
    | exact resolve eq5342 eq5487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5342 eq5487
  have eq17406 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op y y) := by grind
  clear eq17395
  have eq17407 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op y y) := by grind
  clear eq17406
  have eq17426 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17407
       grind)
    | exact superpose eq17407 eq16
    | exact resolve eq16 eq17407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17427 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq83 x (σ y)
       have i₂ := eq17407
       grind)
    | exact superpose eq17407 eq83
    | (have j0 := eq83 x (σ y)
       grind)
    | (have r₁ := eq83 x (σ y)
       have r₂ := eq17407
       grind)
    | exact resolve eq83 eq17407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq17407
  have eq17470 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq17427
  have eq17476 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq17470
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq17470
    | exact resolve eq17470 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17470
  have eq17481 : y = (M.op y y) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq17476
       have i₂ := eq69 y
       grind)
    | exact superpose eq69 eq17476
    | exact resolve eq17476 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq17476
  have eq18701 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq84 y X0
       have i₂ := eq17481
       grind)
    | exact superpose eq17481 eq84
    | (have j0 := eq84 y X0
       grind)
    | (have r₁ := eq84 y x
       have r₂ := eq17481
       grind)
    | exact resolve eq84 eq17481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17481
  have eq18758 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq18701 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18701
  have eq18777 : ∀ X0 : G, (σ (k x y)) = (σ (M.op x x)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq18758 X0
       have j1 := eq84 y X0
       grind)
    | (have r₁ := eq18758 X0
       have r₂ := eq84 y x
       grind)
    | exact resolve eq18758 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18758
  have eq18801 : ∀ X0 : G, (k x y) = (τ (σ (M.op x x))) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq18777 X0
       grind)
    | exact superpose eq18777 eq10
    | (have j1 := eq18777 X0
       grind)
    | exact resolve eq10 eq18777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18777
  have eq18902 : ∀ X0 : G, (k x y) = (M.op x x) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq18801 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq18801
    | (have j0 := eq18801 X0
       grind)
    | exact resolve eq18801 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18801
  have eq19083 : ∀ X0 : G, (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5617 x y
       have i₂ := eq18902 X0
       grind)
    | exact superpose eq18902 eq5617
    | (have j0 := eq5617 x y
       have j1 := eq18902 X0
       grind)
    | (have r₁ := eq5617 x y
       have r₂ := eq18902 X0
       grind)
    | (have r₁ := eq5617 (σ y) (σ y)
       have r₂ := eq18902 (σ y)
       grind)
    | exact resolve eq5617 eq18902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5617 eq18902
  have eq19092 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq19083 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19083
  have eq19100 : ∀ X0 : G, (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (M.op y y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq17426
       have i₂ := eq19092 X0
       grind)
    | exact superpose eq19092 eq17426
    | (have j1 := eq19092 X0
       grind)
    | exact resolve eq17426 eq19092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19092
  have eq19138 : ∀ X0 : G, y = (M.op y y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq19100 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19100
  have eq19359 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op X1 (σ y)) = (k X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 y X0
       have i₂ := eq19138 X1
       grind)
    | exact superpose eq19138 eq84
    | (have j0 := eq84 y X0
       have j1 := eq19138 X0
       grind)
    | exact resolve eq84 eq19138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq19138
  have eq19417 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op X1 (σ y)) = (k X1 (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq19359 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19359
  have eq20355 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq19417 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19417
  have eq20356 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq20355 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20355
  have eq20645 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq20356 (σ X0)
       grind)
    | exact superpose eq20356 eq15
    | exact resolve eq15 eq20356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20356
  have eq21074 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20645 x
       grind)
    | exact superpose eq20645 eq16
    | exact resolve eq16 eq20645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20645
  have eq21357 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq21074
       have i₂ := eq1275 y x
       grind)
    | exact superpose eq1275 eq21074
    | (have j1 := eq1275 y x
       grind)
    | (have r₁ := eq21074
       have r₂ := eq1275 y x
       grind)
    | exact resolve eq21074 eq1275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275
  have eq21358 : (M.op x y) = (M.op x x) := by grind
  clear eq21357
  have eq21603 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq17426
       have i₂ := eq21358
       grind)
    | exact superpose eq21358 eq17426
    | exact resolve eq17426 eq21358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17426 eq21358
  have eq21643 : y = (M.op y y) := by grind
  clear eq21603
  have eq21648 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq21643
       grind)
    | exact superpose eq21643 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq21643
       grind)
    | exact resolve eq12 eq21643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21643
  have eq21712 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq21648 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21648
  have eq22123 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq21074
       have i₂ := eq21712 x
       grind)
    | exact superpose eq21712 eq21074
    | exact resolve eq21074 eq21712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21074 eq21712
  have eq22131 : False := by grind
  exact eq22131
