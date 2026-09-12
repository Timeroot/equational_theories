import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_pyy_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
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
  have eq115 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq48 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 x
       grind)
    | exact resolve eq48 eq22
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
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq175 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq16 X0 X1 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177 X0 X1 X2 X3
       have i₂ := eq16 X2 X1 X0
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq182 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq182 X0 X1
       have i₂ := eq16 X1 y X0
       grind)
    | exact superpose eq16 eq182
    | exact resolve eq182 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq188 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (M.op (M.op X0 (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq191 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq188 x X0
       have i₂ := eq16 X0 sF3 x
       grind)
    | exact superpose eq16 eq188
    | exact resolve eq188 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq596 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by
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
  have eq597 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op (k X0 X1) X2)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq612 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq28 X1 X1
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq621 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq624 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq612 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq612 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq612 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq644 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq596
       grind)
    | exact superpose eq596 eq41
    | exact resolve eq41 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq645 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq644
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq644
    | exact resolve eq644 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq647 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq645
    | exact resolve eq645 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq655 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq647 eq597
    | exact resolve eq597 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq662 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq655
       have r₂ := eq27
       grind)
    | exact resolve eq655 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq666 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq662 eq191
    | exact resolve eq191 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq666
    | (have j0 := eq666 X0 (σ y)
       grind)
    | exact resolve eq666 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq694 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq662 eq669
    | exact resolve eq669 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq705 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq694 eq26
    | (have j1 := eq694 (σ x)
       grind)
    | exact resolve eq26 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq662 eq705
    | exact resolve eq705 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq717 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq710 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq710
       grind)
    | exact resolve eq13 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq717 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq730 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq720 eq710
    | exact resolve eq710 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq735 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq730
  have eq751 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq735 eq142
    | exact resolve eq142 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq752 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq751
    | exact resolve eq751 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq751
  have eq760 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq788 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq621 x x
       have i₂ := eq752
       grind)
    | exact superpose eq752 eq621
    | (have j0 := eq621 x x
       grind)
    | (have r₁ := eq621 x x
       have r₂ := eq752
       grind)
    | exact resolve eq621 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq793 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq788
  have eq795 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq793
       grind)
    | exact superpose eq793 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq793
       grind)
    | exact resolve eq13 eq793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq798 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq795 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq805 : ∀ X0 X1 : G, (M.op x X1) = (M.op x (k (M.op X0 X1) x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x X1 X0
       have i₂ := eq798 (M.op X0 X1)
       grind)
    | exact superpose eq798 eq16
    | exact resolve eq16 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq808 : (M.op x y) = (M.op x (k (M.op x y) x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq798 sF0
       grind)
    | exact superpose eq798 eq175
    | exact resolve eq175 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq818 : (M.op x y) = (M.op x (k (M.op x y) x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq808
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq808
    | exact resolve eq808 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq2379 : ∀ X0 : G, (M.op x x) = (M.op x (k (k X0 x) x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq805 X0 x
       have i₂ := eq798 X0
       grind)
    | exact superpose eq798 eq805
    | exact resolve eq805 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798 eq805
  have eq2403 : ∀ X0 : G, (M.op x x) = (M.op x (k (k X0 x) x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2379 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2379
  have eq2438 : ∀ X0 : G, x = (M.op x (k (k X0 x) x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq793 eq2403
    | exact resolve eq2403 eq793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793 eq2403
  have eq3842 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq662 eq760
    | (have r₁ := eq760
       have r₂ := eq662
       grind)
    | exact resolve eq760 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662 eq760
  have eq3843 : (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3842
  have eq3844 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq647 eq3843
    | exact resolve eq3843 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647 eq3843
  have eq3982 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq694 eq3844
    | exact resolve eq3844 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694 eq3844
  have eq4001 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq3982
  have eq4075 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4001 eq720
    | exact resolve eq720 eq4001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4001
  have eq4089 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq4075
  have eq4353 : (τ (σ y)) = (k (τ (σ y)) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq4089 eq142
    | exact resolve eq142 eq4089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4089
  have eq4384 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | exact superpose eq32 eq4353
    | exact resolve eq4353 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq4353
  have eq4437 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | exact superpose eq4384 eq720
    | exact resolve eq720 eq4384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720 eq4384
  have eq4451 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (k y x) := by grind
  clear eq4437
  have eq4472 : (τ (σ (M.op x y))) = (k y x) ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | exact superpose eq4451 eq115
    | exact resolve eq115 eq4451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq4451
  have eq4499 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | exact superpose eq29 eq4472
    | exact resolve eq4472 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4472
  have eq4640 : x = (M.op x (k (M.op x y) x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq2438 y
       have i₂ := eq4499
       grind)
    | exact superpose eq4499 eq2438
    | exact resolve eq2438 eq4499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4499
  have eq4644 : x = (M.op x (k (M.op x y) x)) ∨ x = (M.op x y) ∨ y = (k y x) := by grind
  clear eq4640
  have eq4655 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | exact superpose eq818 eq4644
    | exact resolve eq4644 eq818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818 eq4644
  have eq4656 : y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq4655
  have eq4676 : x = (M.op x (k y x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2438 y
       have i₂ := eq4656
       grind)
    | exact superpose eq4656 eq2438
    | exact resolve eq2438 eq4656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2438
  have eq4680 : x = (M.op x (k y x)) ∨ x = (M.op x y) := by grind
  clear eq4676
  have eq4689 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4656 eq4680
    | exact resolve eq4680 eq4656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4656 eq4680
  have eq4695 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4689
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4689
    | exact resolve eq4689 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4689
  have eq4696 : x = (M.op x y) := by grind
  clear eq4695
  have eq4698 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4696
       grind)
    | exact superpose eq4696 eq18
    | exact resolve eq18 eq4696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4699 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq4696
       grind)
    | exact superpose eq4696 eq22
    | exact resolve eq22 eq4696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq4705 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4699 eq20
    | exact resolve eq20 eq4699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4699
  have eq4767 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq4698 eq184
    | exact resolve eq184 eq4698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq4768 : (M.op y y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq4698 eq175
    | exact resolve eq175 eq4698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq4781 : ∀ X0 : G, y ≠ (M.op y (M.op x y)) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq4767 y
       grind)
    | exact superpose eq4767 eq13
    | (have j0 := eq13 X0 y
       grind)
    | exact resolve eq13 eq4767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4803 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq4698
       have i₂ := eq4767 sF0
       grind)
    | exact superpose eq4767 eq4698
    | exact resolve eq4698 eq4767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4698
  have eq4820 : ∀ X0 : G, y ≠ (M.op y (M.op x y)) ∨ (k X0 y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq4781 X0
       have i₂ := eq4767 X0
       grind)
    | exact superpose eq4767 eq4781
    | exact resolve eq4781 eq4767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4767 eq4781
  have eq4830 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq4803 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq4803
       grind)
    | exact resolve eq13 eq4803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4838 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq4830 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4830
  have eq4843 : (k y y) = (M.op y (M.op x y)) ∨ y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq4768
       grind)
    | exact superpose eq4768 eq28
    | (have j0 := eq28 y (M.op x y)
       grind)
    | exact resolve eq28 eq4768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4768
  have eq4852 : (k y y) = (M.op y (M.op x y)) := by
    first
    | (have j1 := eq4820 y
       grind)
    | (have r₁ := eq4843
       have r₂ := eq4820 x
       grind)
    | exact resolve eq4843 eq4820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4820 eq4843
  have eq4857 : (k y y) = (k y (M.op x y)) := by
    first
    | exact superpose eq4838 eq4852
    | exact resolve eq4852 eq4838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4852
  have eq4870 : (k (σ y) (σ y)) = (σ (k y (M.op x y))) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq4857
       grind)
    | exact superpose eq4857 eq41
    | exact resolve eq41 eq4857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq4877 : (k (σ y) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq42 eq4870
    | exact resolve eq4870 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4870
  have eq4881 : (k (σ y) (σ x)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq4705 eq4877
    | exact resolve eq4877 eq4705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4877
  have eq4884 : (k (σ y) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq4881
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4881
    | exact resolve eq4881 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4881
  have eq4912 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4838 eq4803
    | exact resolve eq4803 eq4838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4803 eq4838
  have eq4930 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq4912 eq38
    | exact resolve eq38 eq4912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq4912
  have eq4940 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq4930
    | exact resolve eq4930 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4930
  have eq4942 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4705 eq4940
    | exact resolve eq4940 eq4705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4940
  have eq5243 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq4942 eq624
    | (have j0 := eq624 (σ x) X0
       grind)
    | (have r₁ := eq624 (σ x) x
       have r₂ := eq4942
       grind)
    | exact resolve eq624 eq4942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq5245 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4942 eq621
    | (have j0 := eq621 (σ x) (σ x)
       grind)
    | (have r₁ := eq621 (σ x) (σ x)
       have r₂ := eq4942
       grind)
    | exact resolve eq621 eq4942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq5246 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5245
  have eq5247 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq5243 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5243
  have eq5270 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op X0 (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq5246 eq179
    | exact resolve eq179 eq5246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5246
  have eq5278 : ∀ X0 X1 : G, (k X0 (σ x)) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq5247 eq5270
    | exact resolve eq5270 eq5247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5270
  have eq5309 : ∀ X0 X1 X2 : G, (M.op X1 (σ x)) = (M.op X1 (M.op (k X0 (σ x)) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq5247 eq179
    | exact resolve eq179 eq5247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5316 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (k (M.op X0 X1) (σ x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq5247 eq179
    | exact resolve eq179 eq5247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq5342 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (k (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq5247 eq191
    | exact resolve eq191 eq5247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq5348 : ∀ X0 X1 X2 : G, (k X1 (σ x)) = (M.op X1 (M.op (k X0 (σ x)) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq5247 eq5309
    | exact resolve eq5309 eq5247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5247 eq5309
  have eq5918 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq5278
    | (have j0 := eq5278 X0 (σ y)
       grind)
    | exact resolve eq5278 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5278
  have eq6147 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (k (M.op (σ x) (σ y)) (σ x))) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq5342 eq28
    | (have j0 := eq28 X0 (σ y)
       grind)
    | exact resolve eq28 eq5342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6183 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (k (M.op (σ x) (σ y)) (σ x))) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq6147
    | (have j0 := eq6147 X0
       have j1 := eq28 X0 (σ y)
       grind)
    | exact resolve eq6147 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq6147
  have eq7143 : ∀ X0 X1 : G, (M.op X1 (k (k X0 (σ x)) (σ x))) = (M.op X1 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq5918 eq5316
    | exact resolve eq5316 eq5918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5316
  have eq7240 : ∀ X0 X1 : G, (k X1 (σ x)) = (M.op X1 (k (k X0 (σ x)) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq5918 eq7143
    | exact resolve eq7143 eq5918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5918 eq7143
  have eq11676 : (τ (k (σ y) (σ y))) = (k y (τ (k (M.op (σ x) (σ y)) (σ x)))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq6183 eq108
    | (have j1 := eq6183 (σ y)
       grind)
    | exact resolve eq108 eq6183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq6183
  have eq11677 : (τ (k (σ y) (σ y))) = (k y (k (τ (M.op (σ x) (σ y))) x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq142 eq11676
    | exact resolve eq11676 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq11676
  have eq11693 : (τ (k (σ y) (σ y))) = (k y (k (τ (M.op (σ x) (σ y))) (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq11677
       have i₂ := eq4696
       grind)
    | exact superpose eq4696 eq11677
    | exact resolve eq11677 eq4696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4696 eq11677
  have eq11705 : (k y y) = (k y (k (τ (M.op (σ x) (σ y))) (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq116 eq11693
    | exact resolve eq11693 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq11693
  have eq11713 : (k y (M.op x y)) = (k y (k (τ (M.op (σ x) (σ y))) (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq11705
       have i₂ := eq4857
       grind)
    | exact superpose eq4857 eq11705
    | exact resolve eq11705 eq4857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4857 eq11705
  have eq12902 : (σ (k y (M.op x y))) = (k (σ y) (σ (k (τ (M.op (σ x) (σ y))) (M.op x y)))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq11713 eq37
    | exact resolve eq37 eq11713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq11713
  have eq12906 : (σ (k y (M.op x y))) = (k (σ y) (k (σ (τ (M.op (σ x) (σ y)))) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq42 eq12902
    | exact resolve eq12902 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12902
  have eq12907 : (σ (k y (M.op x y))) = (k (σ y) (k (σ (τ (M.op (σ x) (σ y)))) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq4705 eq12906
    | exact resolve eq12906 eq4705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12906
  have eq12908 : (σ (k y (M.op x y))) = (k (σ y) (k (M.op (σ x) (σ y)) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq12907
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq12907
    | exact resolve eq12907 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12907
  have eq12909 : (k (σ y) (σ (M.op x y))) = (k (σ y) (k (M.op (σ x) (σ y)) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq42 eq12908
    | exact resolve eq12908 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq12908
  have eq12910 : (k (σ y) (σ x)) = (k (σ y) (k (M.op (σ x) (σ y)) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq4705 eq12909
    | exact resolve eq12909 eq4705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12909
  have eq12911 : (k (σ y) (σ x)) = (k (σ y) (k (M.op (σ x) (σ y)) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq12910
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12910
    | exact resolve eq12910 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq12910
  have eq12916 : ∀ X0 : G, (M.op X0 (k (M.op (σ x) (σ y)) (σ x))) = (M.op X0 (M.op (k (σ y) (σ x)) X0)) ∨ (σ y) = (M.op (σ y) (k (M.op (σ x) (σ y)) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq12911 eq605
    | (have j0 := eq605 (σ y) (k (M.op (σ x) (σ y)) (σ x)) x
       grind)
    | exact resolve eq605 eq12911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605 eq12911
  have eq12920 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (k (M.op (σ x) (σ y)) (σ x))) ∨ (σ y) = (M.op (σ y) (k (M.op (σ x) (σ y)) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq5348 eq12916
    | exact resolve eq12916 eq5348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5348 eq12916
  have eq12922 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) (k (M.op (σ x) (σ y)) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq5342 eq12920
    | exact resolve eq12920 eq5342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12920
  have eq12924 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq5342 eq12922
    | (have j0 := eq12922 X0
       grind)
    | exact resolve eq12922 eq5342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5342 eq12922
  have eq12925 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq12924 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12924
  have eq12971 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq12925 eq26
    | (have j1 := eq12925 (σ x)
       grind)
    | exact resolve eq26 eq12925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12925
  have eq12992 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4942 eq12971
    | exact resolve eq12971 eq4942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12971
  have eq13017 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq12992 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq12992
       grind)
    | exact resolve eq13 eq12992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13031 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq13017 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13017
  have eq13092 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13031 eq12992
    | exact resolve eq12992 eq13031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12992 eq13031
  have eq13100 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13092
  have eq13105 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4884 eq13100
    | exact resolve eq13100 eq4884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4884 eq13100
  have eq13151 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (k (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq13105 eq7240
    | exact resolve eq7240 eq13105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7240
  have eq13161 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq13105 eq13151
    | exact resolve eq13151 eq13105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13105 eq13151
  have eq13340 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13161 eq26
    | (have j1 := eq13161 (σ x)
       grind)
    | exact resolve eq26 eq13161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq13161
  have eq13363 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4942 eq13340
    | exact resolve eq13340 eq4942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4942 eq13340
  have eq13364 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13363
  have eq13378 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq13364 eq27
    | exact resolve eq27 eq13364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq13364
  have eq13407 : False := by grind
  exact eq13407

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_pxy_pyx_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  clear eq24
  have eq50 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq73 y x
       grind)
    | exact superpose eq73 eq70
    | (have j1 := eq73 y x
       grind)
    | exact resolve eq70 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96
    | exact resolve eq96 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq104
    | exact resolve eq104 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq105
    | exact resolve eq105 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq106 eq73
    | (have j0 := eq73 (σ y) (σ x)
       grind)
    | exact resolve eq73 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq120
    | exact resolve eq120 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq124 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq121
       have r₂ := eq27
       grind)
    | exact resolve eq121 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq126 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq124
    | exact resolve eq124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq223 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq126 eq51
    | exact resolve eq51 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq232 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq223
    | (have j0 := eq223 (σ y)
       grind)
    | exact resolve eq223 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq246 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq126 eq232
    | exact resolve eq232 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq249 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq246
  have eq275 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ x)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq249 eq14
    | exact resolve eq14 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq277 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq275 X0
       have i₂ := eq14 X0 sF2 sF3
       grind)
    | exact superpose eq14 eq275
    | exact resolve eq275 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq290 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq277
    | (have j0 := eq277 (σ x)
       grind)
    | exact resolve eq277 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq329 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq290 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | exact resolve eq13 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq334 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq329 X0
       grind)
    | (have r₁ := eq329 X0
       have r₂ := eq126
       grind)
    | exact resolve eq329 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq329
  have eq376 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq334 eq106
    | exact resolve eq106 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq334
  have eq379 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq376
  have eq382 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq379
    | exact resolve eq379 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq384 : x = (M.op x y) := by
    first
    | (have r₁ := eq382
       have r₂ := eq27
       grind)
    | exact resolve eq382 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq386 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq384 eq20
    | exact resolve eq20 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq388 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq384 eq50
    | exact resolve eq50 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq398 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq386
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq386
    | exact resolve eq386 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq386
  have eq400 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq398 eq26
    | exact resolve eq26 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq441 : (M.op y y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq388 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq388
    | (have j0 := eq388 y
       grind)
    | exact resolve eq388 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq463 : (M.op y x) = (M.op y y) := by
    first
    | exact superpose eq384 eq441
    | exact resolve eq441 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq547 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X0)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq463
       grind)
    | exact superpose eq463 eq14
    | exact resolve eq14 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq548 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq547 X0
       have i₂ := eq14 X0 x y
       grind)
    | exact superpose eq14 eq547
    | exact resolve eq547 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq557 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq548 x
       grind)
    | exact superpose eq548 eq18
    | (have j1 := eq548 x
       grind)
    | exact resolve eq18 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq564 : x = (M.op x x) := by
    first
    | exact superpose eq384 eq557
    | exact resolve eq557 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384 eq557
  have eq570 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq564
       grind)
    | exact superpose eq564 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq564
       grind)
    | exact resolve eq13 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq573 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq570 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq580 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq573 y
       grind)
    | exact superpose eq573 eq70
    | exact resolve eq70 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq573
  have eq585 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq398 eq580
    | exact resolve eq580 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398 eq580
  have eq589 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq585
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq585
    | exact resolve eq585 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq585
  have eq592 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq589
    | exact resolve eq589 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq589
  have eq599 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq592 eq73
    | (have j0 := eq73 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq73 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq592
  have eq600 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq599
  have eq602 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq400 eq600
    | exact resolve eq600 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400 eq600
  have eq605 : False := by grind
  exact eq605

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_pxy_pyx_Equation3532 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  have eq53 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X0 X1 X2 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq16
    | exact resolve eq16 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq73 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq76 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq77 : (k x y) = (τ (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq61
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq61
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq61 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (k x y) = (τ (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq77
    | exact resolve eq77 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq84 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq95 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq91
  have eq96 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq95
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq90
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq90
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq97
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq97
    | exact resolve eq97 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq103
    | exact resolve eq103 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq119 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq122 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq119
  have eq123 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq122
  have eq215 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq215 X0 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq215
    | exact resolve eq215 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq239 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq35
  have eq250 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq239 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq239
    | exact resolve eq239 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq251 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq250
  have eq519 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X2 (σ X0) X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq57
    | exact resolve eq57 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq621 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq251 X0
       grind)
    | exact superpose eq251 eq16
    | exact resolve eq16 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq739 : ∀ X0 X1 X2 : G, (M.op X1 (τ X0)) = (M.op X1 (M.op (τ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X2 (τ X0) X1 (τ X0)
       have i₂ := eq621 X0
       grind)
    | exact superpose eq621 eq57
    | exact resolve eq57 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq781 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ X0)) = (M.op X2 (M.op (σ (k X0 X1)) X3)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 X3 (σ X0) X2 (σ X1)
       have i₂ := eq70 X0 X1
       grind)
    | exact superpose eq70 eq57
    | (have j1 := eq70 X0 X1
       grind)
    | exact resolve eq57 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq6058 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ X1)) = (M.op X2 (M.op (σ (M.op X0 X1)) X3)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq781 X1 X0 X2 X3
       have i₂ := eq11 X1 X0
       grind)
    | exact superpose eq11 eq781
    | (have j0 := eq781 X1 X0 X2 X3
       have j1 := eq11 (σ X1) (σ X0)
       grind)
    | exact resolve eq781 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq10060 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq104 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10061 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq10060
    | exact resolve eq10060 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10060
  have eq10072 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq10061
       have r₂ := eq28
       grind)
    | exact resolve eq10061 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10061
  have eq10078 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq10072 eq57
    | exact resolve eq57 eq10072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10079 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq10072 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq10072
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq10072
       grind)
    | exact resolve eq12 eq10072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10081 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq10079
  have eq10082 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq10081
  have eq10206 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq10082 eq104
    | exact resolve eq104 eq10082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq10082
  have eq10218 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq10206
  have eq10234 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X1 x X0 y
       have i₂ := eq10218
       grind)
    | exact superpose eq10218 eq57
    | exact resolve eq57 eq10218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10235 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq10218
       grind)
    | exact superpose eq10218 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq10218
       grind)
    | exact resolve eq12 eq10218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10237 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq10235
  have eq10238 : y = (k y x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq10237
  have eq10359 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq10238
       grind)
    | exact superpose eq10238 eq90
    | exact resolve eq90 eq10238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq10238
  have eq10379 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10359
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10359
    | exact resolve eq10359 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10359
  have eq10402 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq10379 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq10379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10379
  have eq10403 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq10402
  have eq10407 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq10403
    | exact resolve eq10403 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10403
  have eq10752 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq10407 eq57
    | exact resolve eq57 eq10407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10407
  have eq11002 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq10234 X0 x
       have i₂ := eq10218
       grind)
    | exact superpose eq10218 eq10234
    | exact resolve eq10234 eq10218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10234
  have eq11032 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq11002 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11002
  have eq11036 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11032 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11032
    | (have j0 := eq11032 x
       grind)
    | exact resolve eq11032 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11053 : (σ (M.op y x)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq11032 y
       grind)
    | exact superpose eq11032 eq96
    | exact resolve eq96 eq11032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11032
  have eq11074 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52
       have i₂ := eq11036
       grind)
    | exact superpose eq11036 eq52
    | exact resolve eq52 eq11036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11036
  have eq11099 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq11074
    | exact resolve eq11074 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11074
  have eq11252 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11053
       have i₂ := eq10218
       grind)
    | exact superpose eq10218 eq11053
    | exact resolve eq11053 eq10218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10218 eq11053
  have eq11304 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq11252
  have eq11311 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11304
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11304
    | exact resolve eq11304 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11304
  have eq16272 : (τ (k (σ x) (σ y))) = (M.op y x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16 (M.op y x)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq16332 : (k x y) = (M.op y x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq61 eq16272
    | exact resolve eq16272 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16272
  have eq16996 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq10072 eq10078
    | exact resolve eq10078 eq10072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10078
  have eq17082 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16996 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16996
  have eq17088 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq17082
    | (have j0 := eq17082 (σ x)
       grind)
    | exact resolve eq17082 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17082
  have eq437153 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq11311 eq10752
    | exact resolve eq10752 eq11311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10752 eq11311
  have eq437560 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq437153 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437153
  have eq437586 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq437560
    | (have j0 := eq437560 (σ x)
       grind)
    | exact resolve eq437560 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437560
  have eq438024 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq437586 eq11099
    | exact resolve eq11099 eq437586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq438168 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq438024
  have eq438179 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq438168
       have r₂ := eq28
       grind)
    | exact resolve eq438168 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438168
  have eq841908 : (τ (σ y)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq10072 eq79
    | exact resolve eq79 eq10072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq10072
  have eq842480 : (τ (σ y)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq841908
  have eq842500 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq30 eq842480
    | exact resolve eq842480 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842480
  have eq842521 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq16332
       have i₂ := eq842500
       grind)
    | exact superpose eq842500 eq16332
    | exact resolve eq16332 eq842500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842500
  have eq842619 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq842521
  have eq843030 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y X0)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq842619
       grind)
    | exact superpose eq842619 eq14
    | exact resolve eq14 eq842619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq889460 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq843030 x
       have i₂ := eq842619
       grind)
    | exact superpose eq842619 eq843030
    | exact resolve eq843030 eq842619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842619 eq843030
  have eq890083 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq889460
  have eq890092 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq890083
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq890083
    | exact resolve eq890083 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890083
  have eq890094 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52
       have i₂ := eq890092
       grind)
    | exact superpose eq890092 eq52
    | exact resolve eq52 eq890092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq890166 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X1 x X0 x
       have i₂ := eq890092
       grind)
    | exact superpose eq890092 eq57
    | exact resolve eq57 eq890092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890092
  have eq890201 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq217 eq890166
    | exact resolve eq890166 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq890166
  have eq890244 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq890094
    | exact resolve eq890094 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890094
  have eq891092 : (σ (M.op y x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq890201 y
       grind)
    | exact superpose eq890201 eq96
    | exact resolve eq96 eq890201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq890201
  have eq892290 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ y) (σ y)) X1)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq6058 y x X0 X1
       have i₂ := eq891092
       grind)
    | exact superpose eq891092 eq6058
    | (have j0 := eq6058 y x x x
       grind)
    | exact resolve eq6058 eq891092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6058 eq891092
  have eq892545 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ y) (σ y)) X1)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have j0 := eq892290 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892290
  have eq892628 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq892545 x X0
       have i₂ := eq57 X0 sF3 x sF3
       grind)
    | exact superpose eq57 eq892545
    | exact resolve eq892545 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892545
  have eq892636 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq892628 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq892628
    | (have j0 := eq892628 X0
       grind)
    | exact resolve eq892628 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892628
  have eq892639 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq892636 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq892636
    | (have j0 := eq892636 X0
       grind)
    | exact resolve eq892636 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892636
  have eq892642 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq892639 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq892639
    | (have j0 := eq892639 X0
       grind)
    | exact resolve eq892639 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892639
  have eq892646 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq27 eq892642
    | (have j0 := eq892642 X0
       grind)
    | exact resolve eq892642 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892642
  have eq892647 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq892646 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892646
  have eq892650 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq892647 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq892647
    | (have j0 := eq892647 X0
       grind)
    | exact resolve eq892647 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892647
  have eq892653 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq892650 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq892650
    | (have j0 := eq892650 X0
       grind)
    | exact resolve eq892650 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892650
  have eq892654 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq892653 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892653
  have eq892658 : ∀ X0 : G, x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq892654 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq892654
    | (have j0 := eq892654 X0
       grind)
    | exact resolve eq892654 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892654
  have eq892659 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq892658 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892658
  have eq894317 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq892659
    | (have j0 := eq892659 (σ x)
       grind)
    | exact resolve eq892659 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892659
  have eq895476 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq894317 eq890244
    | exact resolve eq890244 eq894317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890244 eq894317
  have eq895505 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq895476
  have eq895597 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq895505
       have r₂ := eq28
       grind)
    | exact resolve eq895505 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895505
  have eq895611 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq895597 eq84
    | (have r₁ := eq84
       have r₂ := eq895597
       grind)
    | exact resolve eq84 eq895597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq895676 : (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq895597 eq438179
    | exact resolve eq438179 eq895597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438179 eq895597
  have eq895707 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq895676
  have eq895766 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq895611
  have eq895767 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq895766
  have eq896260 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq895707 eq30
    | exact resolve eq30 eq895707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895707
  have eq896456 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq896260
    | exact resolve eq896260 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896260
  have eq896457 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq896456
  have eq896488 : y = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq896457 eq30
    | exact resolve eq30 eq896457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896457
  have eq897644 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq896488
    | exact resolve eq896488 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896488
  have eq898121 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y X0)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq897644 eq53
    | exact resolve eq53 eq897644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897644
  have eq913692 : (τ (σ x)) = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq895767 eq61
    | exact resolve eq61 eq895767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq895767
  have eq913847 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq913692
    | exact resolve eq913692 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913692
  have eq915926 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16332
       have i₂ := eq913847
       grind)
    | exact superpose eq913847 eq16332
    | exact resolve eq16332 eq913847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16332 eq913847
  have eq916049 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq915926
  have eq934167 : (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq898121 x
       have i₂ := eq916049
       grind)
    | exact superpose eq916049 eq898121
    | exact resolve eq898121 eq916049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898121
  have eq934810 : (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq934167
  have eq934816 : (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq934810
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq934810
    | exact resolve eq934810 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934810
  have eq934818 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52
       have i₂ := eq934816
       grind)
    | exact superpose eq934816 eq52
    | exact resolve eq52 eq934816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934816
  have eq934982 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq934818
    | exact resolve eq934818 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934818
  have eq935437 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq934982 eq17088
    | exact resolve eq17088 eq934982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17088 eq934982
  have eq935520 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq935437
  have eq935534 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq935520
       have r₂ := eq28
       grind)
    | exact resolve eq935520 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935520
  have eq935950 : x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq916049
       have i₂ := eq935534
       grind)
    | exact superpose eq935534 eq916049
    | exact resolve eq916049 eq935534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916049 eq935534
  have eq935990 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq935950
  have eq936600 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq935990 eq30
    | exact resolve eq30 eq935990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935990
  have eq936831 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq936600
    | exact resolve eq936600 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936600
  have eq936832 : x = (M.op x y) ∨ x = y := by grind
  clear eq936831
  have eq936862 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq936832 eq21
    | exact resolve eq21 eq936832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq936864 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq936832 eq53
    | exact resolve eq53 eq936832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq936880 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq936832 eq123
    | exact resolve eq123 eq936832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq938076 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq936880
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq936880
    | exact resolve eq936880 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936880
  have eq938092 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq936862
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq936862
    | exact resolve eq936862 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936862
  have eq938155 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq938092 eq27
    | exact resolve eq27 eq938092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq938294 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq938092 eq11099
    | exact resolve eq11099 eq938092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11099
  have eq938615 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq938092 eq437586
    | exact resolve eq437586 eq938092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437586 eq938092
  have eq938883 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq938615
  have eq939204 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq938294
  have eq942309 : ∀ X0 X1 : G, (M.op X0 (τ (σ x))) = (M.op X0 (M.op (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) X1)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq938076 eq739
    | exact resolve eq739 eq938076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938076
  have eq942444 : ∀ X0 : G, (M.op X0 (τ (σ (M.op x y)))) = (M.op X0 (τ (σ x))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq942309 x x
       have i₂ := eq739 sF1 x x
       grind)
    | exact superpose eq739 eq942309
    | exact resolve eq942309 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq942309
  have eq942459 : ∀ X0 : G, (M.op X0 (τ (σ (M.op x y)))) = (M.op X0 x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq29 eq942444
    | exact resolve eq942444 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq942444
  have eq942461 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq31 eq942459
    | exact resolve eq942459 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942459
  have eq970923 : (M.op y y) = (M.op y (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq936864 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq936864
    | (have j0 := eq936864 y
       grind)
    | exact resolve eq936864 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936864
  have eq971581 : (M.op y x) = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq970923 eq942461
    | exact resolve eq942461 eq970923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942461 eq970923
  have eq971594 : (M.op y x) = (M.op y y) ∨ x = y := by grind
  clear eq971581
  have eq972247 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq57 X1 y X0 y
       have i₂ := eq971594
       grind)
    | exact superpose eq971594 eq57
    | exact resolve eq57 eq971594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971594
  have eq972411 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq972247 X0 x
       have i₂ := eq57 x x X0 y
       grind)
    | exact superpose eq57 eq972247
    | exact resolve eq972247 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq972247
  have eq973369 : (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq972411 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq972411
    | (have j0 := eq972411 x
       grind)
    | exact resolve eq972411 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972411
  have eq974674 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq52
       have i₂ := eq973369
       grind)
    | exact superpose eq973369 eq52
    | exact resolve eq52 eq973369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq974737 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq519 x X0 X1
       have i₂ := eq973369
       grind)
    | exact superpose eq973369 eq519
    | exact resolve eq519 eq973369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519 eq973369
  have eq974812 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X1)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq21 eq974737
    | (have j0 := eq974737 X0 X1
       grind)
    | exact resolve eq974737 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974737
  have eq974845 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq974674
    | exact resolve eq974674 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974674
  have eq974860 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq974812 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq974812
    | (have j0 := eq974812 X0 X1
       grind)
    | exact resolve eq974812 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974812
  have eq1093663 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq938155 eq974860
    | exact resolve eq974860 eq938155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938155 eq974860
  have eq1094331 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1093663 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093663
  have eq1474032 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq938883 eq939204
    | exact resolve eq939204 eq938883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938883 eq939204
  have eq1474161 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1474032
  have eq1474210 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1474161
       have r₂ := eq28
       grind)
    | exact resolve eq1474161 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474161
  have eq1474278 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1474210 eq1094331
    | exact resolve eq1094331 eq1474210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094331 eq1474210
  have eq1474283 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq1474278 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474278
  have eq1478960 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq1474283
    | (have j0 := eq1474283 (σ x)
       grind)
    | exact resolve eq1474283 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474283
  have eq1479848 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1478960 eq974845
    | exact resolve eq974845 eq1478960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974845 eq1478960
  have eq1479949 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1479848
  have eq1480066 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1479949
       have r₂ := eq28
       grind)
    | exact resolve eq1479949 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479949
  have eq1481504 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1480066 eq30
    | exact resolve eq30 eq1480066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1480066
  have eq1483119 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq1481504
    | exact resolve eq1481504 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1481504
  have eq1485327 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1483119 eq936832
    | exact resolve eq936832 eq1483119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936832 eq1483119
  have eq1486138 : x = y := by grind
  clear eq1485327
  have eq1487156 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1486138
       grind)
    | exact superpose eq1486138 eq19
    | exact resolve eq19 eq1486138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1487157 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1486138
       grind)
    | exact superpose eq1486138 eq25
    | exact resolve eq25 eq1486138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1486138
  have eq1488211 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1487157
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1487157
    | exact resolve eq1487157 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1487157
  have eq1490396 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1488211 eq27
    | exact resolve eq27 eq1488211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1488211
  have eq1494581 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1490396 eq69
    | exact resolve eq69 eq1490396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq1490396
  have eq1494811 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1494581
       have i₂ := eq1487156
       grind)
    | exact superpose eq1487156 eq1494581
    | exact resolve eq1494581 eq1487156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1487156 eq1494581
  have eq1494888 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1494811 eq15
    | exact resolve eq15 eq1494811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494811
  have eq1495638 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1494888
    | exact resolve eq1494888 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1494888
  have eq1495827 : False := by grind
  exact eq1495827

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxy_pxx_pyx_Equation3532 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3532 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
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
  have eq53 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X0 X1 X2 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq16
    | exact resolve eq16 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq73 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq76 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq77 : (k x y) = (τ (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq61
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq61
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq61 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (k x y) = (τ (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq77
    | exact resolve eq77 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq83 : x ≠ (M.op x y) ∨ x = y ∨ (k x y) = (M.op x x) := by
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
  have eq84 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq95 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq91
  have eq96 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq95
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq90
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq90
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq16
    | exact resolve eq16 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq97
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq97
    | exact resolve eq97 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq103
    | exact resolve eq103 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq119 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq122 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq119
  have eq123 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq122
  have eq129 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq16
    | exact resolve eq16 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq215 X0 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq215
    | exact resolve eq215 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq239 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq35
  have eq250 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq239 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq239
    | exact resolve eq239 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq251 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq250
  have eq519 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X2 (σ X0) X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq57
    | exact resolve eq57 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq621 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq251 X0
       grind)
    | exact superpose eq251 eq16
    | exact resolve eq16 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq739 : ∀ X0 X1 X2 : G, (M.op X1 (τ X0)) = (M.op X1 (M.op (τ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X2 (τ X0) X1 (τ X0)
       have i₂ := eq621 X0
       grind)
    | exact superpose eq621 eq57
    | exact resolve eq57 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq781 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ X0)) = (M.op X2 (M.op (σ (k X0 X1)) X3)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 X3 (σ X0) X2 (σ X1)
       have i₂ := eq70 X0 X1
       grind)
    | exact superpose eq70 eq57
    | (have j1 := eq70 X0 X1
       grind)
    | exact resolve eq57 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq6071 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ X1)) = (M.op X2 (M.op (σ (M.op X0 X1)) X3)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq781 X1 X0 X2 X3
       have i₂ := eq11 X1 X0
       grind)
    | exact superpose eq11 eq781
    | (have j0 := eq781 X1 X0 X2 X3
       have j1 := eq11 (σ X1) (σ X0)
       grind)
    | exact resolve eq781 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq10200 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq104 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10201 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq10200
    | exact resolve eq10200 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10200
  have eq10212 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq10201
       have r₂ := eq28
       grind)
    | exact resolve eq10201 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10201
  have eq10218 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq10212 eq57
    | exact resolve eq57 eq10212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10219 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq10212 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq10212
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq10212
       grind)
    | exact resolve eq12 eq10212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10221 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq10219
  have eq10222 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq10221
  have eq10345 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq10222 eq102
    | exact resolve eq102 eq10222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq10346 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq10222 eq104
    | exact resolve eq104 eq10222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq10222
  have eq10358 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq10346
  have eq10367 : (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq129 eq10345
    | exact resolve eq10345 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10345
  have eq10368 : (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq12 (k y x) (M.op y y)
       grind)
    | (have r₁ := eq10367
       have r₂ := eq12 y x
       grind)
    | exact resolve eq10367 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10367
  have eq10370 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq90
       have i₂ := eq10368
       grind)
    | exact superpose eq10368 eq90
    | exact resolve eq90 eq10368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq10380 : (M.op x y) = (M.op y y) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq10368
       grind)
    | exact superpose eq10368 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq10368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10368
  have eq10381 : (M.op x y) = (M.op y y) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq10380
  have eq10383 : (M.op x y) = (M.op y y) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10381
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10381
    | exact resolve eq10381 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10381
  have eq10392 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10370
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq10370
    | exact resolve eq10370 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10370
  have eq10547 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10392 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq10392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10392
  have eq10548 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10547
  have eq10552 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq10548
    | exact resolve eq10548 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10548
  have eq14473 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq10212 eq10218
    | exact resolve eq10218 eq10212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10218
  have eq14507 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq14473 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14473
  have eq14536 : (τ (M.op (σ y) (σ x))) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq14507 eq129
    | exact resolve eq129 eq14507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq14543 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq14507 eq10358
    | exact resolve eq10358 eq14507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10358 eq14507
  have eq14550 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq14543
  have eq14574 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq14550 eq10212
    | exact resolve eq10212 eq14550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14550
  have eq14583 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq14574
  have eq14587 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq57 X1 x X0 y
       have i₂ := eq14583
       grind)
    | exact superpose eq14583 eq57
    | exact resolve eq57 eq14583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15279 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14587 X0 x
       have i₂ := eq14583
       grind)
    | exact superpose eq14583 eq14587
    | exact resolve eq14587 eq14583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14587
  have eq15317 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq15279 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15279
  have eq15322 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15317 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15317
    | (have j0 := eq15317 x
       grind)
    | exact resolve eq15317 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15341 : (σ (M.op y x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq96
       have i₂ := eq15317 y
       grind)
    | exact superpose eq15317 eq96
    | exact resolve eq96 eq15317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15317
  have eq15513 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq52
       have i₂ := eq15322
       grind)
    | exact superpose eq15322 eq52
    | exact resolve eq52 eq15322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15322
  have eq15543 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq15513
    | exact resolve eq15513 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15513
  have eq15742 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15341
       have i₂ := eq14583
       grind)
    | exact superpose eq14583 eq15341
    | exact resolve eq15341 eq14583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14583 eq15341
  have eq15797 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq15742
  have eq15803 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15797
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15797
    | exact resolve eq15797 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15797
  have eq15817 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq15803 eq10552
    | exact resolve eq10552 eq15803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10552 eq15803
  have eq15834 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq15817
  have eq18425 : (τ (k (σ x) (σ y))) = (M.op y x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16 (M.op y x)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18482 : (k x y) = (M.op y x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq61 eq18425
    | exact resolve eq18425 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18425
  have eq18778 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq10212 eq14536
    | exact resolve eq14536 eq10212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14536
  have eq18831 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq18778
  have eq18843 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq30 eq18831
    | exact resolve eq18831 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18831
  have eq18857 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq10383
       have i₂ := eq18843
       grind)
    | exact superpose eq18843 eq10383
    | exact resolve eq10383 eq18843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10383 eq18843
  have eq18880 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18857
  have eq18899 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq18880
       grind)
    | exact superpose eq18880 eq76
    | exact resolve eq76 eq18880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq18906 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X1 x X0 y
       have i₂ := eq18880
       grind)
    | exact superpose eq18880 eq57
    | exact resolve eq57 eq18880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18917 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq18899
  have eq18921 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18917
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18917
    | exact resolve eq18917 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18917
  have eq19061 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq18906 X0 x
       have i₂ := eq18880
       grind)
    | exact superpose eq18880 eq18906
    | exact resolve eq18906 eq18880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18880 eq18906
  have eq19129 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq19061 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19061
  have eq19136 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19129 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19129
    | (have j0 := eq19129 x
       grind)
    | exact resolve eq19129 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19129
  have eq19217 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52
       have i₂ := eq19136
       grind)
    | exact superpose eq19136 eq52
    | exact resolve eq52 eq19136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19136
  have eq19253 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq19217
    | exact resolve eq19217 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19217
  have eq762507 : (τ (σ y)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq10212 eq79
    | exact resolve eq79 eq10212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq10212
  have eq763087 : (τ (σ y)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq762507
  have eq763111 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq30 eq763087
    | exact resolve eq763087 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763087
  have eq763130 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq18482
       have i₂ := eq763111
       grind)
    | exact superpose eq763111 eq18482
    | exact resolve eq18482 eq763111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763111
  have eq763180 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq763130
  have eq763478 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y X0)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq763180
       grind)
    | exact superpose eq763180 eq14
    | exact resolve eq14 eq763180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq775427 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq763478 x
       have i₂ := eq763180
       grind)
    | exact superpose eq763180 eq763478
    | exact resolve eq763478 eq763180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763180 eq763478
  have eq775912 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq775427
  have eq775928 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq775912
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq775912
    | exact resolve eq775912 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775912
  have eq775930 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52
       have i₂ := eq775928
       grind)
    | exact superpose eq775928 eq52
    | exact resolve eq52 eq775928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq775987 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X1 x X0 x
       have i₂ := eq775928
       grind)
    | exact superpose eq775928 eq57
    | exact resolve eq57 eq775928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775928
  have eq776019 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq217 eq775987
    | exact resolve eq775987 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq775987
  have eq776050 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq775930
    | exact resolve eq775930 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775930
  have eq776801 : (σ (M.op y x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq776019 y
       grind)
    | exact superpose eq776019 eq96
    | exact resolve eq96 eq776019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq776019
  have eq777834 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ y) (σ y)) X1)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq6071 y x X0 X1
       have i₂ := eq776801
       grind)
    | exact superpose eq776801 eq6071
    | (have j0 := eq6071 y x x x
       grind)
    | exact resolve eq6071 eq776801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6071 eq776801
  have eq778089 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ y) (σ y)) X1)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have j0 := eq777834 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777834
  have eq778124 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq778089 x X0
       have i₂ := eq57 X0 sF3 x sF3
       grind)
    | exact superpose eq57 eq778089
    | exact resolve eq778089 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778089
  have eq778132 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq778124 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq778124
    | (have j0 := eq778124 X0
       grind)
    | exact resolve eq778124 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778124
  have eq778135 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq778132 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq778132
    | (have j0 := eq778132 X0
       grind)
    | exact resolve eq778132 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778132
  have eq778138 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq778135 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq778135
    | (have j0 := eq778135 X0
       grind)
    | exact resolve eq778135 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778135
  have eq778140 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq27 eq778138
    | (have j0 := eq778138 X0
       grind)
    | exact resolve eq778138 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778138
  have eq778141 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq778140 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778140
  have eq778143 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq778141 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq778141
    | (have j0 := eq778141 X0
       grind)
    | exact resolve eq778141 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778141
  have eq778145 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq778143 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq778143
    | (have j0 := eq778143 X0
       grind)
    | exact resolve eq778143 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778143
  have eq778146 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq778145 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778145
  have eq778148 : ∀ X0 : G, x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq778146 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq778146
    | (have j0 := eq778146 X0
       grind)
    | exact resolve eq778146 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778146
  have eq778149 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq778148 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778148
  have eq779679 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq778149
    | (have j0 := eq778149 (σ x)
       grind)
    | exact resolve eq778149 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778149
  have eq780933 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq779679 eq776050
    | exact resolve eq776050 eq779679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776050 eq779679
  have eq780962 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq780933
  have eq781051 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq780962
       have r₂ := eq28
       grind)
    | exact resolve eq780962 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780962
  have eq781062 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X0)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq781051 eq54
    | exact resolve eq54 eq781051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq781063 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq781051 eq84
    | (have r₁ := eq84
       have r₂ := eq781051
       grind)
    | exact resolve eq84 eq781051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq781102 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq781063
  have eq781103 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq781102
  have eq781913 : (k x y) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq781103 eq61
    | exact resolve eq61 eq781103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq781928 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq781103 eq18921
    | exact resolve eq18921 eq781103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18921 eq781103
  have eq781982 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq781928
  have eq782014 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq69 eq781913
    | exact resolve eq781913 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781913
  have eq782019 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq782014
       have r₂ := eq83
       grind)
    | exact resolve eq782014 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq782014
  have eq782425 : (k (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq782019
       grind)
    | exact superpose eq782019 eq49
    | exact resolve eq49 eq782019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq782445 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq18482
       have i₂ := eq782019
       grind)
    | exact superpose eq782019 eq18482
    | exact resolve eq18482 eq782019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18482 eq782019
  have eq782504 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq782445
  have eq782550 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq782425
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq782425
    | exact resolve eq782425 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782425
  have eq782689 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq782550 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq782550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782550
  have eq782709 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq782689
  have eq782748 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq782709
    | exact resolve eq782709 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782709
  have eq784568 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq781982 eq19253
    | exact resolve eq19253 eq781982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19253 eq781982
  have eq784727 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq784568
  have eq784783 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq784727 eq30
    | exact resolve eq30 eq784727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784727
  have eq784979 : x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq784783
    | exact resolve eq784783 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784783
  have eq784980 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq784979
  have eq785012 : y = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq784980 eq30
    | exact resolve eq30 eq784980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784980
  have eq786406 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq785012
    | exact resolve eq785012 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785012
  have eq786407 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq786406
  have eq786829 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y X0)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq786407 eq53
    | exact resolve eq53 eq786407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786407
  have eq806142 : (M.op x y) = (M.op x (M.op x x)) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq786829 x
       have i₂ := eq782504
       grind)
    | exact superpose eq782504 eq786829
    | exact resolve eq786829 eq782504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782504 eq786829
  have eq806627 : (M.op x y) = (M.op x (M.op x x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq806142
  have eq806640 : (M.op x y) = (M.op x (M.op x x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq806627
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq806627
    | exact resolve eq806627 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806627
  have eq1385208 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq781062
    | (have j0 := eq781062 (σ y)
       grind)
    | exact resolve eq781062 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781062
  have eq1385734 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq781051 eq1385208
    | exact resolve eq1385208 eq781051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385208
  have eq1385767 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq1385734
  have eq1386033 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ x)) X1)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq1385767 eq57
    | exact resolve eq57 eq1385767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385767
  have eq1386242 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1386033 x X0
       have i₂ := eq57 X0 sF2 x sF3
       grind)
    | exact superpose eq57 eq1386033
    | exact resolve eq1386033 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386033
  have eq1386542 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq1386242
    | (have j0 := eq1386242 (σ x)
       grind)
    | exact resolve eq1386242 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386242
  have eq1387415 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1386542 eq69
    | exact resolve eq69 eq1386542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386542
  have eq1389348 : (M.op x y) = (M.op x (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq806640
       have i₂ := eq1387415
       grind)
    | exact superpose eq1387415 eq806640
    | exact resolve eq806640 eq1387415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806640
  have eq1389381 : (M.op x y) = (M.op x (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq1389348
  have eq1389681 : (M.op x y) = (M.op x (τ (σ x))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq781051 eq1389381
    | exact resolve eq1389381 eq781051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1389381
  have eq1389726 : (M.op x y) = (M.op x (τ (σ x))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq1389681
  have eq1389764 : (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq1389726
    | exact resolve eq1389726 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1389726
  have eq1389949 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1387415
       have i₂ := eq1389764
       grind)
    | exact superpose eq1389764 eq1387415
    | exact resolve eq1387415 eq1389764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387415 eq1389764
  have eq1389976 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq1389949
  have eq1390152 : (M.op x y) = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq781051 eq1389976
    | exact resolve eq1389976 eq781051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781051 eq1389976
  have eq1390736 : (M.op x y) = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq1390152
  have eq1390748 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq1390736
    | exact resolve eq1390736 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390736
  have eq1390749 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1390748
  have eq1390755 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1390749 eq30
    | exact resolve eq30 eq1390749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390749
  have eq1391942 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1390755
    | exact resolve eq1390755 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390755
  have eq1391943 : x = (M.op x y) ∨ x = y := by grind
  clear eq1391942
  have eq1392035 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1391943 eq21
    | exact resolve eq21 eq1391943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1392037 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1391943 eq53
    | exact resolve eq53 eq1391943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1392053 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1391943 eq123
    | exact resolve eq123 eq1391943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq1393842 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq1392053
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq1392053
    | exact resolve eq1392053 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392053
  have eq1393858 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq1392035
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1392035
    | exact resolve eq1392035 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392035
  have eq1394027 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1393858 eq27
    | exact resolve eq27 eq1393858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1394260 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1393858 eq15543
    | exact resolve eq15543 eq1393858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15543
  have eq1394272 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1393858 eq15834
    | exact resolve eq15834 eq1393858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15834
  have eq1394687 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1393858 eq782748
    | exact resolve eq782748 eq1393858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782748 eq1393858
  have eq1394848 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1394687
  have eq1395246 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1394272
  have eq1395250 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1394260
  have eq1395298 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1394848
       have r₂ := eq28
       grind)
    | exact resolve eq1394848 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394848
  have eq1397716 : ∀ X0 X1 : G, (M.op X0 (τ (σ x))) = (M.op X0 (M.op (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) X1)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq1393842 eq739
    | exact resolve eq739 eq1393842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393842
  have eq1397851 : ∀ X0 : G, (M.op X0 (τ (σ (M.op x y)))) = (M.op X0 (τ (σ x))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1397716 x x
       have i₂ := eq739 sF1 x x
       grind)
    | exact superpose eq739 eq1397716
    | exact resolve eq1397716 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq1397716
  have eq1397882 : ∀ X0 : G, (M.op X0 (τ (σ (M.op x y)))) = (M.op X0 x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq29 eq1397851
    | exact resolve eq1397851 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1397851
  have eq1397886 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq31 eq1397882
    | exact resolve eq1397882 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397882
  have eq1439251 : (M.op y y) = (M.op y (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq1392037 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1392037
    | (have j0 := eq1392037 y
       grind)
    | exact resolve eq1392037 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392037
  have eq1439818 : (M.op y x) = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1439251 eq1397886
    | exact resolve eq1397886 eq1439251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397886 eq1439251
  have eq1439831 : (M.op y x) = (M.op y y) ∨ x = y := by grind
  clear eq1439818
  have eq1440137 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y x) X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq57 X1 y X0 y
       have i₂ := eq1439831
       grind)
    | exact superpose eq1439831 eq57
    | exact resolve eq57 eq1439831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439831
  have eq1440306 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1440137 X0 x
       have i₂ := eq57 x x X0 y
       grind)
    | exact superpose eq57 eq1440137
    | exact resolve eq1440137 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1440137
  have eq1443496 : (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq1440306 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1440306
    | (have j0 := eq1440306 x
       grind)
    | exact resolve eq1440306 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440306
  have eq1444434 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq52
       have i₂ := eq1443496
       grind)
    | exact superpose eq1443496 eq52
    | exact resolve eq52 eq1443496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1444540 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq519 x X0 X1
       have i₂ := eq1443496
       grind)
    | exact superpose eq1443496 eq519
    | exact resolve eq519 eq1443496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519 eq1443496
  have eq1444618 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X1)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq21 eq1444540
    | (have j0 := eq1444540 X0 X1
       grind)
    | exact resolve eq1444540 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444540
  have eq1444693 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq1444434
    | exact resolve eq1444434 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444434
  have eq1444708 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ (M.op x y)) X1)) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1444618 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1444618
    | (have j0 := eq1444618 X0 X1
       grind)
    | exact resolve eq1444618 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444618
  have eq1566707 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq1394027 eq1444708
    | exact resolve eq1444708 eq1394027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394027 eq1444708
  have eq1567275 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1566707 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1566707
  have eq2024943 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1395246 eq1395298
    | exact resolve eq1395298 eq1395246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395246 eq1395298
  have eq2024969 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2024943
  have eq2132035 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2024969 eq1395250
    | exact resolve eq1395250 eq2024969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395250 eq2024969
  have eq2132185 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2132035
  have eq2132325 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq2132185 eq1567275
    | exact resolve eq1567275 eq2132185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1567275 eq2132185
  have eq2132330 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq2132325 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2132325
  have eq2132382 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq2132330
    | (have j0 := eq2132330 (σ x)
       grind)
    | exact resolve eq2132330 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2132330
  have eq2133456 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2132382 eq1444693
    | exact resolve eq1444693 eq2132382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444693 eq2132382
  have eq2133556 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2133456
  have eq2133675 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2133556
       have r₂ := eq28
       grind)
    | exact resolve eq2133556 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2133556
  have eq2133691 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq2133675 eq30
    | exact resolve eq30 eq2133675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2133675
  have eq2136113 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq2133691
    | exact resolve eq2133691 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2133691
  have eq2137342 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2136113 eq1391943
    | exact resolve eq1391943 eq2136113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1391943 eq2136113
  have eq2138197 : x = y := by grind
  clear eq2137342
  have eq2139521 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq2138197
       grind)
    | exact superpose eq2138197 eq19
    | exact resolve eq19 eq2138197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2139522 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq2138197
       grind)
    | exact superpose eq2138197 eq25
    | exact resolve eq25 eq2138197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2138197
  have eq2140678 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2139522
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2139522
    | exact resolve eq2139522 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2139522
  have eq2140852 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2140678 eq27
    | exact resolve eq27 eq2140678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2140678
  have eq2142633 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2140852 eq69
    | exact resolve eq69 eq2140852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq2140852
  have eq2142884 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2142633
       have i₂ := eq2139521
       grind)
    | exact superpose eq2139521 eq2142633
    | exact resolve eq2142633 eq2139521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2139521 eq2142633
  have eq2142962 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2142884 eq15
    | exact resolve eq15 eq2142884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2142884
  have eq2143833 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq2142962
    | exact resolve eq2142962 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2142962
  have eq2144073 : False := by grind
  exact eq2144073

/-- `Equation3583`: `x ◇ y = z ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_x_pxy_pyx_Equation3583 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3583 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3583.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
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
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq85 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq86 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq85
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90
    | exact resolve eq90 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq107 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq16
    | exact resolve eq16 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq126 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq137 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq126 eq16
    | exact resolve eq16 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
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
  have eq211 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq59
    | (have j0 := eq59 (σ x) (σ y) X0
       grind)
    | exact resolve eq59 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq210 eq13
    | (have j0 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq210 (M.op x y)
       grind)
    | exact resolve eq13 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq230 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ X0 ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq211 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) X0
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (M.op (σ x) (σ y))
       have r₂ := eq211 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq13 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq233 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j0 := eq224 (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq258 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq233 eq128
    | exact resolve eq128 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq233
  have eq262 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq258
    | exact resolve eq258 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq265 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq262 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq266 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq265
  have eq270 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq266 eq59
    | exact resolve eq59 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq305 : ∀ X0 : G, (σ (M.op x y)) ≠ X0 ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq270 eq13
    | (have j0 := eq13 (σ (M.op x y)) X0
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq270 (σ (M.op x y))
       grind)
    | exact resolve eq13 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq308 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have j0 := eq230 (M.op (σ x) (σ y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq554 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq66
    | (have j0 := eq66 (M.op x y) X0
       grind)
    | exact resolve eq66 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq570 : ∀ X0 : G, (σ (M.op x y)) = (σ (k (M.op x y) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq270 eq554
    | (have j0 := eq554 X0
       grind)
    | exact resolve eq554 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq577 : ∀ X0 : G, (σ (M.op x y)) = (σ (k (M.op x y) X0)) ∨ (σ X0) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq270 eq570
    | (have j0 := eq570 X0
       grind)
    | exact resolve eq570 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq3229 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq577 eq126
    | (have j1 := eq577 x
       grind)
    | exact resolve eq126 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq577
  have eq3265 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq3229
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3229
    | exact resolve eq3229 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3229
  have eq3294 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have j1 := eq305 (σ x)
       grind)
    | (have r₁ := eq3265
       have r₂ := eq305 (σ x)
       grind)
    | (have r₁ := eq3265
       have r₂ := eq305 (k (σ (M.op x y)) (σ x))
       grind)
    | (have r₁ := eq3265
       have r₂ := eq305 (M.op (σ (M.op x y)) (σ x))
       grind)
    | exact resolve eq3265 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq3265
  have eq3321 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq3294
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3294
    | exact resolve eq3294 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3294
  have eq3551 : (τ (σ (M.op x y))) = (k (M.op x y) x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq3321 eq137
    | exact resolve eq137 eq3321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3321
  have eq3555 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq30 eq3551
    | exact resolve eq3551 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3551
  have eq3723 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq3555 eq12
    | (have j0 := eq12 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (σ x)
       have r₂ := eq3555
       grind)
    | exact resolve eq12 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3555
  have eq3726 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (k (M.op x y) x) := by grind
  clear eq3723
  have eq3727 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq3726
       have r₂ := eq13 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq3726 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3726
  have eq4059 : (τ (σ (M.op x y))) = (k (M.op x y) x) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq3727 eq137
    | exact resolve eq137 eq3727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq3727
  have eq4061 : (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq30 eq4059
    | exact resolve eq4059 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4059
  have eq4062 : (M.op x y) = (k (M.op x y) x) := by grind
  clear eq4061
  have eq12566 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12567 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq12566
    | exact resolve eq12566 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12566
  have eq12577 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq12567
       have r₂ := eq27
       grind)
    | exact resolve eq12567 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12567
  have eq12583 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq12577
    | exact resolve eq12577 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12577
  have eq12590 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq12583 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq12583
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq12583
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq12583
       grind)
    | exact resolve eq12 eq12583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12583
  have eq12593 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq12590
  have eq12594 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq12593
       have r₂ := eq51
       grind)
    | exact resolve eq12593 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq12593
  have eq12595 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq12594
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq12594
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq12594
       have r₂ := eq13 x y
       grind)
    | exact resolve eq12594 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12594
  have eq12601 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq12595 eq98
    | exact resolve eq98 eq12595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq12595
  have eq12612 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq12601
  have eq12883 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq59 y x x
       have i₂ := eq12612
       grind)
    | exact superpose eq12612 eq59
    | exact resolve eq59 eq12612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12612
  have eq13492 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12883 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12883
    | (have j0 := eq12883 x
       grind)
    | exact resolve eq12883 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12883
  have eq13507 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13492 eq29
    | exact resolve eq29 eq13492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13492
  have eq13608 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq13507
    | exact resolve eq13507 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq13507
  have eq13609 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq13608
  have eq13829 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13609 eq20
    | exact resolve eq20 eq13609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13882 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13609 eq4062
    | exact resolve eq4062 eq13609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4062 eq13609
  have eq13896 : y = (k y x) := by
    first
    | (have r₁ := eq13882
       have r₂ := eq50
       grind)
    | exact resolve eq13882 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq13882
  have eq13941 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13829
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13829
    | exact resolve eq13829 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13829
  have eq13974 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq85
       have i₂ := eq13896
       grind)
    | exact superpose eq13896 eq85
    | exact resolve eq85 eq13896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq13896
  have eq13997 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13974
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13974
    | exact resolve eq13974 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13974
  have eq14042 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13997 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq13997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13997
  have eq14043 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq14042
    | exact resolve eq14042 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14042
  have eq14053 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq14043
    | exact resolve eq14043 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14043
  have eq14057 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13941 eq26
    | exact resolve eq26 eq13941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13941
  have eq14162 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq270 eq14057
    | exact resolve eq14057 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14057
  have eq14195 : x = (M.op x y) := by
    first
    | (have r₁ := eq14162
       have r₂ := eq27
       grind)
    | exact resolve eq14162 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14162
  have eq14228 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq14195 eq20
    | exact resolve eq20 eq14195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq14340 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq14228
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14228
    | exact resolve eq14228 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14228
  have eq14386 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq14340 eq26
    | exact resolve eq26 eq14340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq19865 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq14340 eq14053
    | exact resolve eq14053 eq14340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14053
  have eq19866 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq19865
       have r₂ := eq27
       grind)
    | exact resolve eq19865 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19865
  have eq19867 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14340 eq19866
    | exact resolve eq19866 eq14340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19866
  have eq19868 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq270 eq19867
    | exact resolve eq19867 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19867
  have eq19874 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq19868 eq308
    | exact resolve eq308 eq19868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308 eq19868
  have eq19923 : (τ (σ y)) = (k y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq19874 eq107
    | exact resolve eq107 eq19874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq19874
  have eq19956 : y = (k y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq19923
    | exact resolve eq19923 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq19923
  have eq20662 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq19956
       grind)
    | exact superpose eq19956 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq19956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19956
  have eq20663 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq20662
  have eq20701 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq59 y y x
       have i₂ := eq20663
       grind)
    | exact superpose eq20663 eq59
    | exact resolve eq59 eq20663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq20663
  have eq21448 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20701 x
       grind)
    | exact superpose eq20701 eq18
    | (have j1 := eq20701 x
       grind)
    | exact resolve eq18 eq20701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq20701
  have eq21449 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq14195 eq21448
    | exact resolve eq21448 eq14195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14195 eq21448
  have eq21518 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq21449 eq14386
    | exact resolve eq14386 eq21449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21449
  have eq21519 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq270 eq21518
    | exact resolve eq21518 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21518
  have eq21569 : x = y := by
    first
    | (have r₁ := eq21519
       have r₂ := eq27
       grind)
    | exact resolve eq21519 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21519
  have eq21716 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq21569
       grind)
    | exact superpose eq21569 eq24
    | exact resolve eq24 eq21569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq21569
  have eq21832 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq21716
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21716
    | exact resolve eq21716 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq21716
  have eq21883 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14340 eq21832
    | exact resolve eq21832 eq14340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14340 eq21832
  have eq23551 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21883 eq14386
    | exact resolve eq14386 eq21883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14386 eq21883
  have eq23552 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq270 eq23551
    | exact resolve eq23551 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq23551
  have eq23602 : False := by grind
  exact eq23602

/-- `Equation3583`: `x ◇ y = z ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_x_pyx_Equation3583 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3583 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3583.models_iff G M).mp hM
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  clear eq44
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
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
  have eq53 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq52 X0 X1 x X3
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq63 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1)) := by
    intro X0 X1
    grind
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
  have eq72 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq73 : x ≠ (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) := by
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
  have eq74 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq16
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq109
    | exact resolve eq109 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq110
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq110
    | exact resolve eq110 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq130 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq207 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 x y X0
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ x) (σ y) X0
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op X0 X0) X1 x
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) := by grind
  have eq225 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq207 eq219
    | exact resolve eq219 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq242 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq35
  have eq249 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by grind
  have eq255 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq208 eq249
    | exact resolve eq249 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq257 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq225 eq130
    | exact resolve eq130 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq225
  have eq261 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq257
    | exact resolve eq257 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq298 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq261 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq299 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq298
  have eq304 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq299 eq53
    | exact resolve eq53 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq353 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq242 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq242
    | (have j0 := eq242 X0 x
       grind)
    | exact resolve eq242 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq377 : (k (k x x) x) = (τ (k (k (σ x) (σ x)) (σ x))) := by
    first
    | exact superpose eq50 eq353
    | exact resolve eq353 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq414 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 X1
       have i₂ := eq53 X0 X1 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq53 eq63
    | exact resolve eq63 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq415 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq414 X0 X1
       have i₂ := eq211 X0 X1
       grind)
    | exact superpose eq211 eq414
    | exact resolve eq414 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq414
  have eq592 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ (k X0 X1)) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq415 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq415
    | (have j1 := eq91 X0 X1
       grind)
    | exact resolve eq415 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq603 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (k (k X0 X1) (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq592 X0 X1
       have i₂ := eq10 (k X0 X1) (k X0 X1)
       grind)
    | exact superpose eq10 eq592
    | (have j0 := eq592 X0 X1
       grind)
    | exact resolve eq592 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq12924 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq111 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq12925 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq12924
    | exact resolve eq12924 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12924
  have eq12936 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq12925
       have r₂ := eq28
       grind)
    | exact resolve eq12925 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12925
  have eq12942 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq12936
    | exact resolve eq12936 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12936
  have eq12951 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq12942 eq53
    | exact resolve eq53 eq12942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12942
  have eq13004 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12951
    | (have j0 := eq12951 (σ x)
       grind)
    | exact resolve eq12951 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12951
  have eq13024 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq415 x x
       have i₂ := eq13004
       grind)
    | exact superpose eq13004 eq415
    | exact resolve eq415 eq13004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415 eq13004
  have eq13046 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq595 y y
       have i₂ := eq13024
       grind)
    | exact superpose eq13024 eq595
    | (have j0 := eq595 y y
       grind)
    | exact resolve eq595 eq13024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595 eq13024
  have eq13049 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13046
  have eq13050 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13049
  have eq13057 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13050
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13050
    | exact resolve eq13050 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13050
  have eq13168 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq13057 eq53
    | exact resolve eq53 eq13057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13057
  have eq13331 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13168 eq27
    | (have j1 := eq13168 (σ x)
       grind)
    | exact resolve eq27 eq13168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13168
  have eq13333 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13331
  have eq13337 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13333 eq208
    | exact resolve eq208 eq13333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13338 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13333 eq255
    | exact resolve eq255 eq13333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13333
  have eq13351 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq13358 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq13337 eq14
    | exact resolve eq14 eq13337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13337
  have eq13504 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13338 eq85
    | exact resolve eq85 eq13338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13338
  have eq13540 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq13504
    | exact resolve eq13504 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13504
  have eq13559 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq13540
       grind)
    | exact superpose eq13540 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq13540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13540
  have eq13560 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13559
  have eq13723 : (k y y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq13727 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq53 y y x
       have i₂ := eq13560
       grind)
    | exact superpose eq13560 eq53
    | exact resolve eq53 eq13560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13560
  have eq13873 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 y X1
       have i₂ := eq13727 (M.op X0 X0)
       grind)
    | exact superpose eq13727 eq14
    | exact resolve eq14 eq13727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13727
  have eq14480 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13351 eq85
    | exact resolve eq85 eq13351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13351
  have eq14524 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27 eq13358
    | (have j0 := eq13358 (σ x) X0
       grind)
    | exact resolve eq13358 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13358
  have eq16089 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13873 x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13873
    | (have j0 := eq13873 x X0
       grind)
    | exact resolve eq13873 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13873
  have eq17433 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14524 eq14480
    | exact resolve eq14480 eq14524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14480 eq14524
  have eq17472 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17433
  have eq17503 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13723
       have i₂ := eq17472
       grind)
    | exact superpose eq17472 eq13723
    | exact resolve eq13723 eq17472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13723 eq17472
  have eq17519 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17503
  have eq18218 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16089 y
       have i₂ := eq17519
       grind)
    | exact superpose eq17519 eq16089
    | exact resolve eq16089 eq17519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16089 eq17519
  have eq18234 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18218
  have eq18253 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18234 eq15
    | exact resolve eq15 eq18234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18234
  have eq18304 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq18253
    | exact resolve eq18253 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18253
  have eq18308 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18304
       have r₂ := eq28
       grind)
    | exact resolve eq18304 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18304
  have eq18314 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18308 eq74
    | (have r₁ := eq74
       have r₂ := eq18308
       grind)
    | exact resolve eq74 eq18308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq18315 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18308 eq208
    | exact resolve eq208 eq18308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq18316 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18308 eq255
    | exact resolve eq255 eq18308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq18308
  have eq18322 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq18314
  have eq18599 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq18315
  have eq18633 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18316 eq50
    | exact resolve eq50 eq18316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq18316
  have eq18674 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq18633
    | exact resolve eq18633 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18633
  have eq18960 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq18674
       grind)
    | exact superpose eq18674 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq18674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18674
  have eq18961 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq18960
  have eq19003 : (k x x) = (M.op x x) ∨ x = (M.op x y) := by grind
  have eq19007 : ∀ X0 : G, x = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq53 x x x
       have i₂ := eq18961
       grind)
    | exact superpose eq18961 eq53
    | exact resolve eq53 eq18961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18961
  have eq19621 : (k (k x x) x) = (τ (k (M.op (σ x) (σ x)) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18599 eq377
    | exact resolve eq377 eq18599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq18599
  have eq19651 : (k (k x x) x) = (τ (M.op (σ x) (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by grind
  clear eq19621
  have eq19652 : (τ (M.op (σ x) (σ x))) = (k (k x x) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19651
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | exact superpose eq53 eq19651
    | exact resolve eq19651 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19651
  have eq29327 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18322 eq80
    | exact resolve eq80 eq18322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq18322
  have eq29356 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq29327
    | exact resolve eq29327 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29327
  have eq29805 : (τ (M.op (σ x) (σ x))) = (k (M.op x x) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19652
       have i₂ := eq19003
       grind)
    | exact superpose eq19003 eq19652
    | exact resolve eq19652 eq19003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19003 eq19652
  have eq29830 : (τ (M.op (σ x) (σ x))) = (k (M.op x x) x) ∨ x = (M.op x y) := by grind
  clear eq29805
  have eq29839 : (τ (M.op (σ x) (σ x))) = (M.op x (M.op x x)) ∨ x = (M.op x y) := by grind
  clear eq29830
  have eq29845 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29839
       have i₂ := eq53 x x x
       grind)
    | exact superpose eq53 eq29839
    | exact resolve eq29839 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29839
  have eq29853 : (τ (σ y)) = (M.op x x) ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29356 eq29845
    | exact resolve eq29845 eq29356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29356 eq29845
  have eq29924 : (τ (σ y)) = (M.op x x) ∨ x = (M.op x y) ∨ y = (k y x) := by grind
  clear eq29853
  have eq29931 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (k y x) := by
    first
    | exact superpose eq30 eq29924
    | exact resolve eq29924 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29924
  have eq29935 : y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq29931
       have r₂ := eq73
       grind)
    | exact resolve eq29931 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq29931
  have eq29942 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq29935
       grind)
    | exact superpose eq29935 eq70
    | exact resolve eq70 eq29935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq29956 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq29935
       grind)
    | exact superpose eq29935 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq29935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29935
  have eq29957 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq29956
  have eq29959 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq29957
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29957
    | exact resolve eq29957 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29957
  have eq29972 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq29942
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq29942
    | exact resolve eq29942 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29942
  have eq29974 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29959
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq29959
    | exact resolve eq29959 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29959
  have eq30598 : x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19007 x
       have i₂ := eq29974
       grind)
    | exact superpose eq29974 eq19007
    | exact resolve eq19007 eq29974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19007
  have eq30618 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq53 x x x
       have i₂ := eq29974
       grind)
    | exact superpose eq29974 eq53
    | exact resolve eq53 eq29974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29974
  have eq30633 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq30598
  have eq30674 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30633 eq21
    | exact resolve eq21 eq30633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30633
  have eq30829 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq30674
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq30674
    | exact resolve eq30674 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30674
  have eq31572 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30829 eq27
    | exact resolve eq27 eq30829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30829
  have eq31773 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq304 eq31572
    | exact resolve eq31572 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31572
  have eq31805 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq31773
       have r₂ := eq28
       grind)
    | exact resolve eq31773 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31773
  have eq59337 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq30618 x
       grind)
    | exact superpose eq30618 eq19
    | (have j1 := eq30618 x
       grind)
    | exact resolve eq19 eq30618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30618
  have eq59350 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq59337
  have eq59522 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq59350
  have eq59524 : x = (M.op x y) := by
    first
    | (have r₁ := eq59522
       have r₂ := eq31805
       grind)
    | exact resolve eq59522 eq31805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31805 eq59522
  have eq59639 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq59524 eq21
    | exact resolve eq21 eq59524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq59678 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | exact superpose eq59524 eq207
    | exact resolve eq207 eq59524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq59856 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq59639
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq59639
    | exact resolve eq59639 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59639
  have eq59885 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq59856 eq27
    | exact resolve eq27 eq59856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60013 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq59856 eq29972
    | exact resolve eq29972 eq59856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29972
  have eq64195 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq60013
       have i₂ := eq59678 x
       grind)
    | exact superpose eq59678 eq60013
    | exact resolve eq60013 eq59678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59678 eq60013
  have eq64207 : (τ (σ y)) = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq64195 eq90
    | exact resolve eq90 eq64195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq64195
  have eq64239 : (τ (σ y)) = (k y x) ∨ x = y := by
    first
    | exact superpose eq59524 eq64207
    | exact resolve eq64207 eq59524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64207
  have eq64255 : y = (k y x) ∨ x = y := by
    first
    | exact superpose eq30 eq64239
    | exact resolve eq64239 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64239
  have eq64287 : (σ y) = (σ (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq603 y x
       have i₂ := eq64255
       grind)
    | exact superpose eq64255 eq603
    | (have j0 := eq603 y x
       grind)
    | exact resolve eq603 eq64255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq64255
  have eq64294 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq64287
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq64287
    | exact resolve eq64287 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq64287
  have eq64312 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq64294
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq64294
    | exact resolve eq64294 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64294
  have eq64328 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq64312
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq64312
    | exact resolve eq64312 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64312
  have eq64336 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq64328
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq64328
    | exact resolve eq64328 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64328
  have eq64341 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq27 eq64336
    | exact resolve eq64336 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq64336
  have eq64345 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq59856 eq64341
    | exact resolve eq64341 eq59856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64341
  have eq64349 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq64345
       have r₂ := eq28
       grind)
    | exact resolve eq64345 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64345
  have eq64353 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq64349
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq64349
    | exact resolve eq64349 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64349
  have eq64357 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq59856 eq64353
    | exact resolve eq64353 eq59856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64353
  have eq64361 : (σ y) = (σ (M.op x y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq304 eq64357
    | exact resolve eq64357 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64357
  have eq64364 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq64361
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq64361
    | exact resolve eq64361 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64361
  have eq74954 : (τ (σ y)) = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq64364 eq85
    | exact resolve eq85 eq64364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq64364
  have eq74997 : y = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq30 eq74954
    | exact resolve eq74954 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq74954
  have eq75998 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq74997
       grind)
    | exact superpose eq74997 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq74997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74997
  have eq75999 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq75998
  have eq78661 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq53 y y x
       have i₂ := eq75999
       grind)
    | exact superpose eq75999 eq53
    | exact resolve eq53 eq75999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq75999
  have eq79578 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq19
       have i₂ := eq78661 x
       grind)
    | exact superpose eq78661 eq19
    | (have j1 := eq78661 x
       grind)
    | exact resolve eq19 eq78661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq78661
  have eq79592 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq59524 eq79578
    | exact resolve eq79578 eq59524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59524 eq79578
  have eq79593 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq79592
  have eq79727 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq79593 eq59885
    | exact resolve eq59885 eq79593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79593
  have eq79757 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq304 eq79727
    | exact resolve eq79727 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79727
  have eq79819 : x = y := by
    first
    | (have r₁ := eq79757
       have r₂ := eq28
       grind)
    | exact resolve eq79757 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79757
  have eq79965 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq79819
       grind)
    | exact superpose eq79819 eq25
    | exact resolve eq25 eq79819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq79819
  have eq80209 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq79965
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq79965
    | exact resolve eq79965 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq79965
  have eq80314 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq59856 eq80209
    | exact resolve eq80209 eq59856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59856 eq80209
  have eq81404 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq80314 eq59885
    | exact resolve eq59885 eq80314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59885 eq80314
  have eq81411 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq304 eq81404
    | exact resolve eq81404 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304 eq81404
  have eq81471 : False := by grind
  exact eq81471

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_x_pxy_Equation3600 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3600 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
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
  have eq22 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
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
  have eq37 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq35 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq35
    | exact resolve eq35 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq64 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq95 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq31
  have eq108 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq95 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq95
    | exact resolve eq95 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq338 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq89 x y
       grind)
    | exact superpose eq89 eq16
    | (have j1 := eq89 x y
       grind)
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 : G, (k X0 (τ (σ (k X0 X0)))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq108 X0
       have i₂ := eq89 X0 X0
       grind)
    | exact superpose eq89 eq108
    | (have j1 := eq89 X0 X0
       grind)
    | exact resolve eq108 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq341 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq352 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq89 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq352 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq355 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq341 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq357 : ∀ X0 : G, (k X0 (τ (σ (k X0 X0)))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq339 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq364 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq355 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq355
    | (have j0 := eq355 X0
       grind)
    | exact resolve eq355 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq366 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq357 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq357
    | (have j0 := eq357 X0
       grind)
    | exact resolve eq357 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq517 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq353 (M.op X0 X1)
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq353
    | (have j0 := eq353 (M.op X0 X1)
       grind)
    | exact resolve eq353 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq353 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq353
    | (have j0 := eq353 (τ X0)
       grind)
    | exact resolve eq353 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq522 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq517 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq524 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq521 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq521
    | (have j0 := eq521 X0
       grind)
    | exact resolve eq521 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq527 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq524 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq524
    | (have j0 := eq524 X0
       grind)
    | exact resolve eq524 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq553 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k (k X0 (k X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 (k X0 (k X0 X0)) X1
       have i₂ := eq364 X0
       grind)
    | exact superpose eq364 eq89
    | (have j0 := eq89 X0 X0
       have j1 := eq364 X0
       grind)
    | exact resolve eq89 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq364
  have eq587 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq527 (τ X0)
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq527
    | (have j0 := eq527 (τ X0)
       grind)
    | exact resolve eq527 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq683 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
       have i₂ := eq522 X0 X1
       grind)
    | exact superpose eq522 eq37
    | exact resolve eq37 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq892 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq338
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq338
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq338 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq893 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq892
  have eq1168 : ∀ X0 : G, (k X0 (τ (σ X0))) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq108 X0
       have i₂ := eq366 X0
       grind)
    | exact superpose eq366 eq108
    | (have j1 := eq366 X0
       grind)
    | exact resolve eq108 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq366
  have eq1190 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1168 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1168
    | (have j0 := eq1168 X0
       grind)
    | exact resolve eq1168 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq1264 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1190 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq1190
    | exact resolve eq1190 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1280 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (k (τ X0) (τ X0))
       have i₂ := eq1190 (τ X0)
       grind)
    | exact superpose eq1190 eq18
    | (have j1 := eq1190 (τ X0)
       grind)
    | exact resolve eq18 eq1190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1190
  have eq1286 : ∀ X0 : G, (σ (τ X0)) = (k X0 (k (σ (τ X0)) X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1280 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq1280
    | (have j0 := eq1280 X0
       grind)
    | exact resolve eq1280 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280
  have eq1299 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1264 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq1264
    | (have j0 := eq1264 X0
       grind)
    | exact resolve eq1264 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264
  have eq1302 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1286 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1286
    | (have j0 := eq1286 X0
       grind)
    | exact resolve eq1286 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286
  have eq1314 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1302 X0
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq1302
    | (have j0 := eq1302 X0
       grind)
    | exact resolve eq1302 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302
  have eq1913 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) (k X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 (k X0 X0) X1
       have i₂ := eq1314 X0
       grind)
    | exact superpose eq1314 eq19
    | (have j1 := eq1314 X0
       grind)
    | exact resolve eq19 eq1314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314
  have eq1923 : ∀ X0 X1 : G, (k X0 (k X0 X0)) = X0 ∨ (k (σ X1) X0) = (k (σ X1) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1913 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1913
    | (have j0 := eq1913 X0 X1
       grind)
    | exact resolve eq1913 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1913
  have eq2532 : ∀ X0 X1 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq587 (M.op X0 X1)
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq587
    | (have j0 := eq587 (M.op X0 X1)
       grind)
    | exact resolve eq587 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq2543 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq2532 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2532
  have eq15318 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq42 y x
       have i₂ := eq893
       grind)
    | exact superpose eq893 eq42
    | exact resolve eq42 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq19016 : ∀ X0 : G, (σ X0) ≠ (k (σ X0) (σ X0)) ∨ (k (σ X0) (σ X0)) = (k (σ X0) (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq1923 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1923
  have eq19019 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) (σ X0)) = (k (σ X0) (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq19016 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq19016
    | (have j0 := eq19016 X0
       grind)
    | exact resolve eq19016 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19016
  have eq19056 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (k X0 (k (τ (σ X0)) X0))) ∨ (σ X0) ≠ (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq19019 X0
       have i₂ := eq22 (σ X0) X0 X0
       grind)
    | exact superpose eq22 eq19019
    | (have j0 := eq19019 X0
       grind)
    | exact resolve eq19019 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq19019
  have eq19092 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (k X0 (k X0 X0))) ∨ (σ X0) ≠ (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq19056 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19056
    | (have j0 := eq19056 X0
       grind)
    | exact resolve eq19056 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19056
  have eq19128 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq19092 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq19092
    | (have j0 := eq19092 X0
       grind)
    | exact resolve eq19092 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19092
  have eq29755 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq19128 X0
       have i₂ := eq1299 X0
       grind)
    | exact superpose eq1299 eq19128
    | (have j1 := eq1299 X0
       grind)
    | (have r₁ := eq19128 X0
       have r₂ := eq1299 X0
       grind)
    | exact resolve eq19128 eq1299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299 eq19128
  have eq29774 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have j0 := eq29755 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29755
  have eq29775 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have j0 := eq29774 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29774
  have eq30133 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (k (k X0 (k X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (k X0 X0)) X1
       have i₂ := eq29775 X0
       grind)
    | exact superpose eq29775 eq15
    | exact resolve eq15 eq29775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29775
  have eq30229 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (k (k X0 (k X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30133 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq30133
    | exact resolve eq30133 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30133
  have eq79850 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k (k X0 (k X0 X0)) X0)) := by
    intro X0
    first
    | (have j0 := eq553 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq79852 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k (k X0 (k X0 X0)) X0)) := by
    intro X0
    first
    | (have j0 := eq79850 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79850
  have eq79853 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k (k X0 (k X0 X0)) X0)) := by
    intro X0
    first
    | (have j0 := eq79852 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79852
  have eq79858 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq79853 X0
       have i₂ := eq30229 X0 X0
       grind)
    | exact superpose eq30229 eq79853
    | (have j0 := eq79853 X0
       grind)
    | exact resolve eq79853 eq30229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30229 eq79853
  have eq80272 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq42 (σ X0) (σ X0)
       have i₂ := eq79858 X0
       grind)
    | exact superpose eq79858 eq42
    | (have j1 := eq79858 X0
       grind)
    | exact resolve eq42 eq79858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq80294 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq79858 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79858
  have eq80306 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq80272 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq80272
    | (have j0 := eq80272 X0
       grind)
    | exact resolve eq80272 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80272
  have eq80349 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq80306 X0
       have j1 := eq80294 X0
       grind)
    | (have r₁ := eq80306 X0
       have r₂ := eq80294 X0
       grind)
    | exact resolve eq80306 eq80294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80294 eq80306
  have eq80686 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq80349 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq80349
    | exact resolve eq80349 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81082 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq80686 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq80686
    | exact resolve eq80686 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq80686
  have eq81148 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq81082 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81082
    | exact resolve eq81082 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81082
  have eq81473 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq64 X0 X0
       have i₂ := eq81148 (τ X0)
       grind)
    | exact superpose eq81148 eq64
    | exact resolve eq64 eq81148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq81555 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq81473 X0
       have i₂ := eq81148 X0
       grind)
    | exact superpose eq81148 eq81473
    | exact resolve eq81473 eq81148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81473
  have eq1005982 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2543 (σ y) (σ x)
       have i₂ := eq15318
       grind)
    | exact superpose eq15318 eq2543
    | exact resolve eq2543 eq15318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2543 eq15318
  have eq1006219 : (τ (σ y)) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1005982
       have i₂ := eq81555 (σ y)
       grind)
    | exact superpose eq81555 eq1005982
    | exact resolve eq1005982 eq81555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81555 eq1005982
  have eq1006412 : (τ (σ y)) = (τ (σ (k y y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1006219
       have i₂ := eq80349 y
       grind)
    | exact superpose eq80349 eq1006219
    | exact resolve eq1006219 eq80349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006219
  have eq1006598 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1006412
       have i₂ := eq10 (k y y)
       grind)
    | exact superpose eq10 eq1006412
    | exact resolve eq1006412 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006412
  have eq1006729 : (τ (σ y)) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1006598
       have i₂ := eq81148 y
       grind)
    | exact superpose eq81148 eq1006598
    | exact resolve eq1006598 eq81148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006598
  have eq1006801 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1006729
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1006729
    | exact resolve eq1006729 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006729
  have eq1006853 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq527 y
       grind)
    | (have r₁ := eq1006801
       have r₂ := eq527 y
       grind)
    | exact resolve eq1006801 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527 eq1006801
  have eq1006883 : (σ y) = (σ (k x x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1006853
       have i₂ := eq80349 x
       grind)
    | exact superpose eq80349 eq1006853
    | exact resolve eq1006853 eq80349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80349 eq1006853
  have eq1006898 : y = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1006883
       have i₂ := eq81148 x
       grind)
    | exact superpose eq81148 eq1006883
    | exact resolve eq1006883 eq81148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81148 eq1006883
  have eq1007004 : ∀ X0 : G, y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq37 y y x
       have i₂ := eq1006898
       grind)
    | exact superpose eq1006898 eq37
    | exact resolve eq37 eq1006898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006898
  have eq1007354 : ∀ X0 X1 : G, (σ y) = (σ (M.op x x)) ∨ y = (M.op X0 y) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq37 x x x
       have i₂ := eq1007004 X0
       grind)
    | exact superpose eq1007004 eq37
    | (have j1 := eq1007004 X0
       grind)
    | exact resolve eq37 eq1007004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007004
  have eq1007892 : ∀ X0 X1 : G, (M.op x x) = (τ (σ y)) ∨ y = (M.op X0 y) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1007354 X0 X1
       grind)
    | exact superpose eq1007354 eq10
    | (have j1 := eq1007354 X0 X0
       grind)
    | exact resolve eq10 eq1007354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007354
  have eq1008628 : ∀ X0 X1 : G, y = (M.op x x) ∨ y = (M.op X0 y) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1007892 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1007892
    | (have j0 := eq1007892 X0 X0
       grind)
    | exact resolve eq1007892 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007892
  have eq1011326 : ∀ X0 X1 X2 : G, y = (M.op X2 y) ∨ y = (M.op X1 y) ∨ y = (M.op X0 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37 x x x
       have i₂ := eq1008628 X0 X1
       grind)
    | exact superpose eq1008628 eq37
    | (have j1 := eq1008628 X2 X2
       grind)
    | exact resolve eq37 eq1008628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq1008628
  have eq1014083 : ∀ X0 X1 : G, y ≠ y ∨ y = (M.op X1 y) ∨ y = (M.op X0 y) := by
    intro X0 X1
    first
    | (have j0 := eq1011326 X1 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011326
  have eq1014084 : ∀ X0 X1 : G, y = (M.op X1 y) ∨ y = (M.op X0 y) := by
    intro X0 X1
    first
    | (have j0 := eq1014083 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014083
  have eq1014533 : ∀ X0 : G, y ≠ y ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1014084 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014084
  have eq1014534 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1014533 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014533
  have eq1016793 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) := by
    intro X1
    first
    | (have i₁ := eq683 x y x
       have i₂ := eq1014534 x
       grind)
    | exact superpose eq1014534 eq683
    | exact resolve eq683 eq1014534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq1017763 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1016793 (σ x)
       grind)
    | exact superpose eq1016793 eq16
    | exact resolve eq16 eq1016793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016793
  have eq1017945 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1017763
       have i₂ := eq1014534 x
       grind)
    | exact superpose eq1014534 eq1017763
    | exact resolve eq1017763 eq1014534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014534 eq1017763
  have eq1017946 : False := by grind
  exact eq1017946

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_x_pxy_pyx_Equation3600 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3600 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
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
  have eq85 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq86 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq85
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq85
       grind)
    | exact superpose eq85 eq16
    | exact resolve eq16 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90
    | exact resolve eq90 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq101 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq86
       grind)
    | exact superpose eq86 eq16
    | exact resolve eq16 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq130 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq222 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
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
  have eq223 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq61
    | (have j0 := eq61 (σ x) (σ y) X0
       grind)
    | exact resolve eq61 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq222 eq13
    | (have j0 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq222 (M.op x y)
       grind)
    | exact resolve eq13 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq273 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ X0 ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq223 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) X0
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (M.op (σ x) (σ y))
       have r₂ := eq223 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq13 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq320 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j0 := eq243 (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq322 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq320 eq130
    | exact resolve eq130 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq320
  have eq326 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq322
    | exact resolve eq322 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq329 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq326 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq330 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq329
  have eq333 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq330 eq61
    | exact resolve eq61 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq345 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have j0 := eq273 (M.op (σ x) (σ y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq813 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq814 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq813
    | exact resolve eq813 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813
  have eq817 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq814
       have r₂ := eq27
       grind)
    | exact resolve eq814 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq819 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq817
    | exact resolve eq817 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq821 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq819
    | exact resolve eq819 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq829 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq821 eq345
    | exact resolve eq345 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq821
  have eq916 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq829 eq108
    | exact resolve eq108 eq829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq829
  have eq920 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq916
    | exact resolve eq916 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq971 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq920
       grind)
    | exact superpose eq920 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq972 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq971
  have eq978 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq61 y y x
       have i₂ := eq972
       grind)
    | exact superpose eq972 eq61
    | exact resolve eq61 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq972
  have eq1048 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq978 x
       grind)
    | exact superpose eq978 eq18
    | (have j1 := eq978 x
       grind)
    | exact resolve eq18 eq978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq1049 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1048
  have eq1055 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1049 eq51
    | (have r₁ := eq51
       have r₂ := eq1049
       grind)
    | exact resolve eq51 eq1049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1049
  have eq1062 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1055
  have eq1190 : (τ (σ y)) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1062 eq95
    | exact resolve eq95 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq1062
  have eq1197 : y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1190
    | exact resolve eq1190 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1190
  have eq1200 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1197
       have r₂ := eq50
       grind)
    | exact resolve eq1197 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197
  have eq1204 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq1200
       grind)
    | exact superpose eq1200 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq1205 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1204
  have eq1207 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1205
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1205
    | exact resolve eq1205 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq1208 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1207
  have eq1212 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1208
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1208
    | exact resolve eq1208 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1208
  have eq1214 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1212 eq20
    | exact resolve eq20 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq1241 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1214
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1214
    | exact resolve eq1214 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1293 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1241 eq26
    | exact resolve eq26 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq1326 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq333 eq1293
    | exact resolve eq1293 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293
  have eq1330 : x = (M.op x y) := by
    first
    | (have r₁ := eq1326
       have r₂ := eq27
       grind)
    | exact resolve eq1326 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326
  have eq1389 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1330 eq20
    | exact resolve eq20 eq1330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1391 : x ≠ x ∨ y = (k y x) := by
    first
    | exact superpose eq1330 eq50
    | (have r₁ := eq50
       have r₂ := eq1330
       grind)
    | exact resolve eq50 eq1330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1330
  have eq1406 : y = (k y x) := by grind
  clear eq1391
  have eq1417 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1389
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1389
    | exact resolve eq1389 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1389
  have eq1419 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1417 eq26
    | exact resolve eq26 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1578 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq85
       have i₂ := eq1406
       grind)
    | exact superpose eq1406 eq85
    | exact resolve eq85 eq1406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq1406
  have eq1583 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1417 eq1578
    | exact resolve eq1578 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1578
  have eq1586 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1583
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1583
    | exact resolve eq1583 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1583
  have eq1617 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1586 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq1586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1618 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq1617
  have eq1620 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1419 eq1618
    | exact resolve eq1618 eq1419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1618
  have eq1623 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1419 eq1620
    | exact resolve eq1620 eq1419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1620
  have eq1626 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1623
       have r₂ := eq27
       grind)
    | exact resolve eq1623 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623
  have eq1738 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1626 eq101
    | (have r₁ := eq101
       have r₂ := eq1626
       grind)
    | exact resolve eq101 eq1626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq1626
  have eq1744 : (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by grind
  clear eq1738
  have eq1745 : (σ (M.op x y)) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1417 eq1744
    | exact resolve eq1744 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1744
  have eq1747 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1417 eq1745
    | exact resolve eq1745 eq1417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417 eq1745
  have eq1749 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq333 eq1747
    | exact resolve eq1747 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747
  have eq1750 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1586 eq1749
    | exact resolve eq1749 eq1586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1586 eq1749
  have eq1751 : (σ (M.op x y)) = (σ y) := by grind
  clear eq1750
  have eq1769 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1751 eq1419
    | exact resolve eq1419 eq1751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419 eq1751
  have eq1772 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq333 eq1769
    | exact resolve eq1769 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333 eq1769
  have eq1783 : False := by grind
  exact eq1783
