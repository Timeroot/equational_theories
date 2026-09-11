import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1687`: `x = (y ◇ x) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxy_pyx_pxy_Equation1687 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1687 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1687.models_iff G M).mp hM
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
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
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
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
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq45
    | (have j0 := eq45 (M.op x y)
       grind)
    | exact resolve eq45 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
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
  have eq117 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq48
    | (have j0 := eq48 (M.op x y)
       grind)
    | exact resolve eq48 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq132 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq51
    | (have j0 := eq51 x
       grind)
    | exact resolve eq51 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq51
    | (have j0 := eq51 y
       grind)
    | exact resolve eq51 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
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
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq73
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq175 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) y)) := by
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
  have eq176 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X0) = (M.op X0 (M.op (M.op (M.op (M.op X0 X2) X0) X3) (M.op (M.op X0 X2) X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X0 X2) X0) (M.op x X0) X3
       have i₂ := eq16 X0 x X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) (M.op X0 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X2 X0) X1 (M.op (M.op X0 x) X0)
       have i₂ := eq16 X0 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 (M.op (M.op X0 X2) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (M.op X0 X2) X0) X1 X0
       have i₂ := eq16 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op y (M.op x y))) := by
    intro X0
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op (M.op x y) x)) x) := by
    intro X0
    first
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) (σ x)) := by
    intro X0
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : ∀ X0 X1 : G, (k X0 (M.op (M.op X0 X1) X0)) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq183 (M.op (M.op X0 x) X0)
       have i₂ := eq16 X0 (M.op X0 x) x
       grind)
    | exact superpose eq16 eq183
    | exact resolve eq183 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k (M.op X0 X0) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 X0
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq16
    | exact resolve eq16 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : (σ y) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ y) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq176 sF3
       have i₂ := eq183 sF3
       grind)
    | exact superpose eq183 eq176
    | exact resolve eq176 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : (M.op (M.op x y) x) = (M.op x x) := by
    first
    | exact superpose eq178 eq188
    | exact resolve eq188 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq585 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq179 eq192
    | exact resolve eq192 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq594 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq585 eq179
    | exact resolve eq179 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq585
  have eq642 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op (M.op X1 X2) X1)) = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq662 : (M.op x y) = (k x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF2 sF3
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq684 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq700 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq28 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq728 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq662
       grind)
    | exact superpose eq662 eq41
    | exact resolve eq41 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq729 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq728
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq728
    | exact resolve eq728 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq731 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq729
    | exact resolve eq729 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq741 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq731 eq672
    | exact resolve eq672 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq748 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq741
       have r₂ := eq27
       grind)
    | exact resolve eq741 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq754 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq748 eq594
    | exact resolve eq594 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq756 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq748 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq748
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq748
       grind)
    | exact resolve eq12 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq748 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq760 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq756
  have eq761 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq757
    | exact resolve eq757 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq762 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq731 eq760
    | exact resolve eq760 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731 eq760
  have eq773 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq754 eq176
    | exact resolve eq176 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq776 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq754 eq16
    | exact resolve eq16 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq778 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq776
    | (have j0 := eq776 X0
       grind)
    | exact resolve eq776 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq779 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq773
    | exact resolve eq773 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq781 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq779 eq186
    | exact resolve eq186 eq779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq782 : (M.op (σ y) (M.op (σ x) (σ y))) = (k (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq779 eq183
    | exact resolve eq183 eq779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq788 : (M.op (σ x) (σ y)) = (M.op (σ y) (k (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq782 eq781
    | exact resolve eq781 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781 eq782
  have eq794 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq778 eq16
    | exact resolve eq16 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq811 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq788 eq16
    | exact resolve eq16 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq817 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq779 eq794
    | exact resolve eq794 eq779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779 eq794
  have eq827 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq817
  have eq836 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq827 eq183
    | exact resolve eq183 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq899 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq761 eq142
    | exact resolve eq142 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq761
  have eq900 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq899
    | exact resolve eq899 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq906 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq762 eq827
    | exact resolve eq827 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq911 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq762 eq183
    | exact resolve eq183 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq919 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq906
  have eq922 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq911
    | exact resolve eq911 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq927 : (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq919 eq922
    | exact resolve eq922 eq919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq931 : x = (M.op y (M.op (M.op x y) x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq178 y
       have i₂ := eq919
       grind)
    | exact superpose eq919 eq178
    | exact resolve eq178 eq919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq966 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq927 eq153
    | exact resolve eq153 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq969 : x = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30 eq966
    | exact resolve eq966 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966
  have eq972 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq662 eq969
    | exact resolve eq969 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq988 : x = (M.op y (M.op (M.op x y) x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq178 y
       have i₂ := eq972
       grind)
    | exact superpose eq972 eq178
    | exact resolve eq178 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq989 : y ≠ y ∨ x = (M.op y y) ∨ y = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq972
       grind)
    | exact superpose eq972 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq972
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq972
       grind)
    | exact resolve eq12 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq990 : y = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq972
       grind)
    | exact superpose eq972 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq993 : y = (k x y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq989
  have eq994 : x = (M.op x y) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq990
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq990
    | exact resolve eq990 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq995 : y = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq994
  have eq999 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq995
       grind)
    | exact superpose eq995 eq40
    | exact resolve eq40 eq995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1000 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq999
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq999
    | exact resolve eq999 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999
  have eq1105 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq988 eq175
    | exact resolve eq175 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1109 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq988 eq16
    | exact resolve eq16 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq1111 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1109 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1109
    | (have j0 := eq1109 X0
       grind)
    | exact resolve eq1109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109
  have eq1112 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1105
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1105
    | exact resolve eq1105 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq1113 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1112
       have i₂ := eq28 sF0 sF0
       grind)
    | exact superpose eq28 eq1112
    | (have j1 := eq28 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq1112 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1114 : (M.op x y) = (M.op y (M.op y (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1112 eq184
    | exact resolve eq184 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1115 : (k y (M.op x y)) = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1112 eq183
    | exact resolve eq183 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1121 : (M.op x y) = (M.op y (k y (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1115 eq1114
    | exact resolve eq1114 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq1151 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1111 eq16
    | exact resolve eq16 eq1111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1190 : y = (M.op (M.op x y) (M.op (M.op x y) y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1121 eq175
    | exact resolve eq175 eq1121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1193 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op (M.op x y) y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1121 eq16
    | exact resolve eq16 eq1121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121
  have eq1245 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1112 eq1151
    | exact resolve eq1151 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151
  have eq1259 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1245
  have eq1272 : (k (M.op x y) y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq183 y
       have i₂ := eq1259
       grind)
    | exact superpose eq1259 eq183
    | exact resolve eq183 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1295 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq931 eq175
    | exact resolve eq175 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1302 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1295
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1295
    | exact resolve eq1295 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295
  have eq1306 : (M.op x y) = (M.op y (M.op y (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1302 eq184
    | exact resolve eq184 eq1302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1307 : (k y (M.op x y)) = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1302 eq183
    | exact resolve eq183 eq1302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1315 : (M.op x y) = (M.op y (k y (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1307 eq1306
    | exact resolve eq1306 eq1307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306
  have eq1379 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op (M.op x y) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1302 eq180
    | exact resolve eq180 eq1302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1471 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq931 eq181
    | exact resolve eq181 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq1529 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq181 X0 (M.op x X0) X1
       have i₂ := eq16 X0 x X1
       grind)
    | exact superpose eq16 eq181
    | exact resolve eq181 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq1580 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1471 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1471
    | (have j0 := eq1471 X0
       grind)
    | exact resolve eq1471 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471
  have eq1636 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op y (M.op (M.op (M.op (M.op x y) y) X0) (M.op (M.op x y) y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1190 eq16
    | exact resolve eq16 eq1190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190
  have eq1638 : (M.op (M.op x y) y) = (M.op y (M.op (M.op (M.op x y) y) (M.op (M.op x y) y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1636 x
       have i₂ := eq1529 (M.op sF0 y) x
       grind)
    | exact superpose eq1529 eq1636
    | exact resolve eq1636 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1636
  have eq1644 : (M.op y y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1193 eq1638
    | exact resolve eq1638 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193 eq1638
  have eq1648 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1259 eq1644
    | exact resolve eq1644 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1644
  have eq1930 : (M.op x y) = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1272 eq1648
    | exact resolve eq1648 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648
  have eq1934 : y = (M.op (k (M.op x y) y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1272 eq1111
    | exact resolve eq1111 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111
  have eq1939 : ∀ X0 : G, (k (M.op x y) y) = (M.op (M.op X0 (k (M.op x y) y)) (M.op y (k (M.op x y) y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1272 eq180
    | exact resolve eq180 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272
  have eq1943 : y = (M.op (k (M.op x y) y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1934
  have eq1947 : (M.op x y) = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1930
  have eq2021 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1302 eq1580
    | exact resolve eq1580 eq1302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1580
  have eq2043 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2021
  have eq2059 : (k (M.op x y) y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq183 y
       have i₂ := eq2043
       grind)
    | exact superpose eq2043 eq183
    | exact resolve eq183 eq2043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2081 : (M.op x y) = (M.op (k y (M.op x y)) (k y (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1307 eq184
    | exact resolve eq184 eq1307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq1307
  have eq2101 : ∀ X0 : G, (k y (M.op x y)) = (M.op (M.op x y) (M.op (M.op (k y (M.op x y)) X0) (k y (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1315 eq16
    | exact resolve eq16 eq1315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315
  have eq2109 : (k y (M.op x y)) = (M.op (M.op x y) (M.op (k y (M.op x y)) (k y (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2101 x
       have i₂ := eq1529 (k y sF0) x
       grind)
    | exact superpose eq1529 eq2101
    | exact resolve eq2101 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2101
  have eq2114 : (k y (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2081 eq2109
    | exact resolve eq2109 eq2081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2081 eq2109
  have eq2116 : y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1302 eq2114
    | exact resolve eq2114 eq1302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302 eq2114
  have eq2123 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2116 eq42
    | exact resolve eq42 eq2116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2116
  have eq2130 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2123
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2123
    | exact resolve eq2123 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2123
  have eq2361 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (M.op (σ x) X0) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1000 eq642
    | (have j0 := eq642 (σ y) (σ x) x
       grind)
    | exact resolve eq642 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000
  have eq2536 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2361 x
       have i₂ := eq1529 sF2 x
       grind)
    | exact superpose eq1529 eq2361
    | exact resolve eq2361 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2361
  have eq2560 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq2536
    | exact resolve eq2536 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2536
  have eq2842 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) (M.op (M.op (σ x) (σ y)) (σ y)))) ∨ y = (M.op y x) := by
    intro X1
    first
    | exact superpose eq811 eq16
    | exact resolve eq16 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2858 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y)))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2842 x
       have i₂ := eq1529 (M.op sF4 sF3) x
       grind)
    | exact superpose eq1529 eq2842
    | exact resolve eq2842 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2842
  have eq2872 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq811 eq2858
    | exact resolve eq2858 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811 eq2858
  have eq2879 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq827 eq2872
    | exact resolve eq2872 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827 eq2872
  have eq2886 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2879 eq836
    | exact resolve eq836 eq2879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836 eq2879
  have eq2906 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq2886
  have eq2915 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2906 eq153
    | exact resolve eq153 eq2906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq2906
  have eq3873 : ∀ X0 : G, (M.op y (k (M.op x y) y)) = (M.op (k (M.op x y) y) (M.op (M.op (M.op y (k (M.op x y) y)) X0) (M.op y (k (M.op x y) y)))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1943 eq177
    | exact resolve eq177 eq1943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1943
  have eq3891 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op y (M.op (M.op (M.op (M.op x y) y) X0) (M.op (M.op x y) y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq177 y y x
       have i₂ := eq2043
       grind)
    | exact superpose eq2043 eq177
    | exact resolve eq177 eq2043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq4035 : (M.op (M.op x y) y) = (M.op y (M.op (M.op (M.op x y) y) (M.op (M.op x y) y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq3891 x
       have i₂ := eq1529 (M.op sF0 y) x
       grind)
    | exact superpose eq1529 eq3891
    | exact resolve eq3891 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3891
  have eq4049 : (M.op y (k (M.op x y) y)) = (M.op (k (M.op x y) y) (M.op (M.op y (k (M.op x y) y)) (M.op y (k (M.op x y) y)))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3873 x
       have i₂ := eq1529 (M.op y (k sF0 y)) x
       grind)
    | exact superpose eq1529 eq3873
    | exact resolve eq3873 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3873
  have eq4122 : (M.op y y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1379 eq4035
    | exact resolve eq4035 eq1379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1379 eq4035
  have eq4136 : (M.op y (k (M.op x y) y)) = (M.op (k (M.op x y) y) (k (M.op x y) y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1939 eq4049
    | exact resolve eq4049 eq1939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1939 eq4049
  have eq4177 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2043 eq4122
    | exact resolve eq4122 eq2043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2043 eq4122
  have eq4191 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1947 eq4136
    | exact resolve eq4136 eq1947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4136
  have eq4207 : y = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1112 eq4191
    | exact resolve eq4191 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4191
  have eq4268 : (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4177 eq2059
    | exact resolve eq2059 eq4177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059 eq4177
  have eq4291 : (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq4268
  have eq4347 : y = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4207 eq1115
    | exact resolve eq1115 eq4207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115 eq4207
  have eq4371 : y = (k y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq4347
  have eq4395 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4291 eq41
    | exact resolve eq41 eq4291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq4291
  have eq4405 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq4395
    | exact resolve eq4395 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4395
  have eq4760 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2130 eq700
    | (have j0 := eq700 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq700 (σ y) (σ (M.op x y))
       have r₂ := eq2130
       grind)
    | exact resolve eq700 eq2130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130
  have eq4773 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq4760
  have eq4800 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4405 eq4773
    | exact resolve eq4773 eq4405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4405 eq4773
  have eq4801 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4800
  have eq8416 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq562 eq1529
    | exact resolve eq1529 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq10175 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq993
       grind)
    | exact superpose eq993 eq36
    | exact resolve eq36 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq993
  have eq10181 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10175
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10175
    | exact resolve eq10175 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10175
  have eq10183 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1259 eq10181
    | exact resolve eq10181 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259 eq10181
  have eq10184 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq10183
  have eq10348 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10184 eq672
    | exact resolve eq672 eq10184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672 eq10184
  have eq10385 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq10348 eq180
    | exact resolve eq180 eq10348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq10348
  have eq10400 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq26 eq10385
    | (have j0 := eq10385 X0
       grind)
    | exact resolve eq10385 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10385
  have eq10943 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1113 eq183
    | exact resolve eq183 eq1113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq1113
  have eq10979 : y = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1112 eq10943
    | exact resolve eq10943 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112 eq10943
  have eq10980 : y = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq10979
  have eq10988 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10980 eq42
    | exact resolve eq42 eq10980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq10980
  have eq10993 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq10988
    | exact resolve eq10988 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10988
  have eq10995 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10993
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10993
    | exact resolve eq10993 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq10993
  have eq11002 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ y) (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10995 eq642
    | (have j0 := eq642 (σ (M.op x y)) (σ (M.op x y)) x
       grind)
    | exact resolve eq642 eq10995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11004 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11002 x
       have i₂ := eq1529 sF1 x
       grind)
    | exact superpose eq1529 eq11002
    | exact resolve eq11002 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11002
  have eq11008 : (σ (M.op x y)) = (M.op (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq11004
    | (have j1 := eq28 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11004 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11004
  have eq11011 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10995 eq11008
    | exact resolve eq11008 eq10995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11008
  have eq11236 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2560 eq176
    | exact resolve eq176 eq2560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq2560
  have eq11264 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq11236
    | exact resolve eq11236 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11236
  have eq11271 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq8416 eq11264
    | exact resolve eq11264 eq8416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11264
  have eq12988 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10400 eq1529
    | (have j1 := eq10400 (σ x)
       grind)
    | exact resolve eq1529 eq10400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10400
  have eq13031 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq8416 eq12988
    | exact resolve eq12988 eq8416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8416 eq12988
  have eq13044 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq11271 eq13031
    | exact resolve eq13031 eq11271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11271 eq13031
  have eq13060 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13044 eq186
    | exact resolve eq186 eq13044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq13044
  have eq14308 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11011 eq13060
    | exact resolve eq13060 eq11011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11011 eq13060
  have eq14347 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq14308
  have eq14371 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq14347
       have r₂ := eq27
       grind)
    | exact resolve eq14347 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14347
  have eq14393 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq14371 eq16
    | exact resolve eq16 eq14371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14413 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14393 x
       have i₂ := eq555 sF1 x
       grind)
    | exact superpose eq555 eq14393
    | exact resolve eq14393 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14393
  have eq14418 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14413 x
       have i₂ := eq1529 sF1 x
       grind)
    | exact superpose eq1529 eq14413
    | exact resolve eq14413 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14413
  have eq14419 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq14371 eq14418
    | exact resolve eq14418 eq14371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14371 eq14418
  have eq14420 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq10995 eq14419
    | exact resolve eq14419 eq10995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10995 eq14419
  have eq14421 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq14420
  have eq14423 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14421 eq32
    | exact resolve eq32 eq14421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14428 : (k y x) = (τ (k (σ x) (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14421 eq115
    | exact resolve eq115 eq14421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14430 : (k y (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14421 eq117
    | exact resolve eq117 eq14421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq14431 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14421 eq133
    | exact resolve eq133 eq14421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq14421
  have eq14549 : (k (M.op x y) x) = (k (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq132 eq14431
    | exact resolve eq14431 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14431
  have eq14550 : (k x (M.op x y)) = (k y (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq100 eq14430
    | exact resolve eq14430 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq14430
  have eq14552 : (k x x) = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq98 eq14428
    | exact resolve eq14428 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq14428
  have eq14557 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq14423
    | exact resolve eq14423 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14423
  have eq14561 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1947 eq14549
    | exact resolve eq14549 eq1947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1947 eq14549
  have eq14562 : y = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4371 eq14550
    | exact resolve eq14550 eq4371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4371 eq14550
  have eq14563 : y = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq995 eq14552
    | exact resolve eq14552 eq995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995 eq14552
  have eq14568 : x = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14557 eq14562
    | exact resolve eq14562 eq14557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14562
  have eq14569 : x = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14557 eq14563
    | exact resolve eq14563 eq14557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14557 eq14563
  have eq14878 : x ≠ x ∨ (M.op x y) = (M.op x x) ∨ x = (k (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14568 eq700
    | (have j0 := eq700 x (M.op x y)
       grind)
    | (have r₁ := eq700 x (M.op x y)
       have r₂ := eq14568
       grind)
    | exact resolve eq700 eq14568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700 eq14568
  have eq14881 : (M.op x y) = (M.op x x) ∨ x = (k (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq14878
  have eq14883 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (k (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq14881
       have i₂ := eq573
       grind)
    | exact superpose eq573 eq14881
    | exact resolve eq14881 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14881
  have eq14884 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq14883
  have eq14888 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14561 eq14884
    | exact resolve eq14884 eq14561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14561 eq14884
  have eq14889 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq14888
  have eq14913 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq684 x
       have i₂ := eq14569
       grind)
    | exact superpose eq14569 eq684
    | (have j0 := eq684 x
       grind)
    | (have r₁ := eq684 x
       have r₂ := eq14569
       grind)
    | exact resolve eq684 eq14569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14569
  have eq14916 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq14913
  have eq14937 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq14916
       have i₂ := eq573
       grind)
    | exact superpose eq573 eq14916
    | exact resolve eq14916 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14916
  have eq14955 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14889 eq14937
    | exact resolve eq14937 eq14889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14889 eq14937
  have eq14956 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq14955
  have eq14976 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14956 eq29
    | exact resolve eq29 eq14956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq14982 : (k (M.op x y) x) = (τ (k (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14956 eq132
    | exact resolve eq132 eq14956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq14956
  have eq14989 : (k y x) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115 eq14982
    | exact resolve eq14982 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq14982
  have eq14995 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq14976
    | exact resolve eq14976 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14976
  have eq14998 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq14995
       grind)
    | exact superpose eq14995 eq18
    | exact resolve eq18 eq14995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15005 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq662
       have i₂ := eq14995
       grind)
    | exact superpose eq14995 eq662
    | exact resolve eq662 eq14995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq15006 : (M.op x y) = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq900
       have i₂ := eq14995
       grind)
    | exact superpose eq14995 eq900
    | exact resolve eq900 eq14995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq15091 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2915
       have i₂ := eq14995
       grind)
    | exact superpose eq14995 eq2915
    | exact resolve eq2915 eq14995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2915 eq14995
  have eq15276 : ∀ X0 : G, x = (M.op (k (M.op x y) x) (M.op (M.op x X0) x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq642 y x X0
       have i₂ := eq14989
       grind)
    | exact superpose eq14989 eq642
    | (have j0 := eq642 (M.op x y) x X0
       grind)
    | exact resolve eq642 eq14989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642 eq14989
  have eq15286 : x = (M.op (k (M.op x y) x) (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15276 x
       have i₂ := eq1529 x x
       grind)
    | exact superpose eq1529 eq15276
    | exact resolve eq15276 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15276
  have eq15294 : x = (M.op (k (M.op x y) x) (M.op (M.op x y) x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15286
       have i₂ := eq573
       grind)
    | exact superpose eq573 eq15286
    | exact resolve eq15286 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15286
  have eq15300 : x = (M.op x y) ∨ x = (M.op (k (M.op x y) x) (M.op (M.op x y) x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15294
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15294
    | exact resolve eq15294 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15294
  have eq15301 : x = (M.op (k (M.op x y) x) (M.op (M.op x y) x)) ∨ x = (M.op x y) := by grind
  clear eq15300
  have eq16881 : x = (M.op (k (M.op x y) x) (k (M.op x y) x)) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq15301
       have i₂ := eq28 sF0 x
       grind)
    | exact superpose eq28 eq15301
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq15301 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq16901 : (M.op x (k (M.op x y) x)) = (M.op (k (M.op x y) x) (k (M.op x y) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15301 eq1529
    | exact resolve eq1529 eq15301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15301
  have eq16911 : x = (M.op (k (M.op x y) x) (k (M.op x y) x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14998 eq16881
    | exact resolve eq16881 eq14998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16881
  have eq16912 : x = (M.op (k (M.op x y) x) (k (M.op x y) x)) ∨ x = (M.op x y) := by grind
  clear eq16911
  have eq16936 : ∀ X0 : G, (k (M.op x y) x) = (M.op x (M.op (M.op (k (M.op x y) x) X0) (k (M.op x y) x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16912 eq16
    | exact resolve eq16 eq16912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16942 : (k (M.op x y) x) = (M.op x (k x (k (M.op x y) x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16912 eq560
    | exact resolve eq560 eq16912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq16951 : x = (M.op x (k (M.op x y) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16912 eq1529
    | exact resolve eq1529 eq16912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16912
  have eq16959 : (k (M.op x y) x) = (M.op x (M.op (k (M.op x y) x) (k (M.op x y) x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16936 x
       have i₂ := eq1529 (k sF0 x) x
       grind)
    | exact superpose eq1529 eq16936
    | exact resolve eq16936 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16936
  have eq16968 : (k (M.op x y) x) = (M.op x (M.op x (k (M.op x y) x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16901 eq16959
    | exact resolve eq16959 eq16901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16901 eq16959
  have eq16975 : (k (M.op x y) x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16951 eq16968
    | exact resolve eq16968 eq16951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16951 eq16968
  have eq16981 : (k (M.op x y) x) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16975
       have i₂ := eq573
       grind)
    | exact superpose eq573 eq16975
    | exact resolve eq16975 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16975
  have eq20405 : (M.op x x) = (M.op (k (M.op x y) x) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16942 eq1529
    | exact resolve eq1529 eq16942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16942
  have eq20409 : (M.op (M.op x y) x) = (M.op (k (M.op x y) x) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20405
       have i₂ := eq573
       grind)
    | exact superpose eq573 eq20405
    | exact resolve eq20405 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573 eq20405
  have eq20424 : (k (M.op x y) x) = (M.op (k (M.op x y) x) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16981 eq20409
    | exact resolve eq20409 eq16981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16981 eq20409
  have eq25249 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4801 eq1529
    | exact resolve eq1529 eq4801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4801
  have eq25250 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq25249
  have eq27026 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15006 eq20424
    | exact resolve eq20424 eq15006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15006 eq20424
  have eq27035 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq27026
  have eq27076 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27035 eq178
    | exact resolve eq178 eq27035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27035
  have eq27213 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27076 eq1529
    | exact resolve eq1529 eq27076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27076
  have eq27240 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14998 eq27213
    | exact resolve eq27213 eq14998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27213
  have eq27241 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq27240
  have eq27339 : (τ (σ x)) = (k (τ (σ x)) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27241 eq15091
    | exact resolve eq15091 eq27241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15091 eq27241
  have eq27348 : (τ (σ x)) = (k (τ (σ x)) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq27339
  have eq27369 : x = (k x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq27348
    | exact resolve eq27348 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27348
  have eq27415 : x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15005 eq27369
    | exact resolve eq27369 eq15005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15005 eq27369
  have eq27416 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq27415
  have eq27504 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27416 eq178
    | exact resolve eq178 eq27416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq27416
  have eq27635 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27504 eq1529
    | exact resolve eq1529 eq27504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27504
  have eq27657 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14998 eq27635
    | exact resolve eq27635 eq14998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14998 eq27635
  have eq27658 : x = (M.op x y) := by grind
  clear eq27657
  have eq27680 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq27658
       grind)
    | exact superpose eq27658 eq18
    | exact resolve eq18 eq27658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq27681 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq27658
       grind)
    | exact superpose eq27658 eq22
    | exact resolve eq22 eq27658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq27746 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27681 eq20
    | exact resolve eq20 eq27681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27681
  have eq27834 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27746 eq25250
    | exact resolve eq25250 eq27746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25250
  have eq27857 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq27834
    | exact resolve eq27834 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27834
  have eq27858 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq27857
  have eq27941 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27858 eq27
    | exact resolve eq27 eq27858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27858
  have eq28079 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq27941
       have r₂ := eq27746
       grind)
    | exact resolve eq27941 eq27746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27941
  have eq28119 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq28079 eq26
    | exact resolve eq26 eq28079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq28120 : y = (τ (σ x)) := by
    first
    | exact superpose eq28079 eq32
    | exact resolve eq32 eq28079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq28079
  have eq28351 : x = y := by
    first
    | exact superpose eq30 eq28120
    | exact resolve eq28120 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq28120
  have eq28407 : y = (M.op x y) := by
    first
    | (have i₁ := eq28351
       have i₂ := eq27658
       grind)
    | exact superpose eq27658 eq28351
    | exact resolve eq28351 eq27658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27658 eq28351
  have eq28493 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq28407
       grind)
    | exact superpose eq28407 eq175
    | exact resolve eq175 eq28407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq28626 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq27680
       have i₂ := eq28407
       grind)
    | exact superpose eq28407 eq27680
    | exact resolve eq27680 eq28407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27680 eq28407
  have eq28664 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq28493 x
       have i₂ := eq555 sF0 x
       grind)
    | exact superpose eq555 eq28493
    | exact resolve eq28493 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555 eq28493
  have eq28685 : (M.op x y) = (k (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq28664 x
       have i₂ := eq1529 sF0 x
       grind)
    | exact superpose eq1529 eq28664
    | exact resolve eq28664 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529 eq28664
  have eq28691 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq28626 eq28685
    | exact resolve eq28685 eq28626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28626 eq28685
  have eq29169 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq28691 eq38
    | exact resolve eq38 eq28691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq28691
  have eq29184 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq29169
    | exact resolve eq29169 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq29169
  have eq29186 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq27746 eq29184
    | exact resolve eq29184 eq27746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29184
  have eq29374 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq29186 eq684
    | (have j0 := eq684 (σ x)
       grind)
    | (have r₁ := eq684 (σ x)
       have r₂ := eq29186
       grind)
    | exact resolve eq684 eq29186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684 eq29186
  have eq29377 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq29374
  have eq29415 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29377 eq28119
    | exact resolve eq28119 eq29377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28119 eq29377
  have eq29486 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq29415 eq27
    | exact resolve eq27 eq29415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq29415
  have eq29619 : False := by grind
  exact eq29619

/-- `Equation1687`: `x = (y ◇ x) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_y_pyy_pyx_Equation1687 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1687 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1687.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
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
  have eq47 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) y)) := by
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
  have eq48 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op (M.op x y) x)) := by
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
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) (M.op X0 (M.op X2 X0))) := by
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
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 (M.op (M.op X0 X2) X0)) X0) := by
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
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k X0 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    grind
  have eq58 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq70 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq74 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq70
  have eq82 : x ≠ (M.op x y) ∨ y = (M.op x x) ∨ (M.op x x) = (k y x) := by
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
  have eq83 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
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
  clear eq37
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq94
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq94
    | exact resolve eq94 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq116 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq118 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq134 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq116 eq16
    | exact resolve eq16 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq118
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq118
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq118 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq164 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq156
  have eq212 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op y (M.op x y))) := by
    intro X0
    first
    | exact superpose eq47 eq14
    | exact resolve eq14 eq47
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
  clear eq35
  have eq373 : (M.op y (M.op x y)) = (k (M.op x y) (M.op y (M.op x y))) := by
    first
    | exact superpose eq47 eq54
    | exact resolve eq54 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377 : x = (k (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq50 eq54
    | exact resolve eq54 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq402 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x)))) := by
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq453 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 (M.op x X0) X1
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq511 : (M.op (M.op x y) x) = (M.op x x) := by
    first
    | (have i₁ := eq453 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq453
    | (have j0 := eq453 x y
       grind)
    | exact resolve eq453 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq512 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq47 eq453
    | exact resolve eq453 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq453
    | (have j0 := eq453 (σ x) (σ y)
       grind)
    | exact resolve eq453 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq514 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq48 eq453
    | exact resolve eq453 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq525 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq453 X0 x
       grind)
    | exact superpose eq453 eq14
    | exact resolve eq14 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) (M.op x y)) := by
    first
    | exact superpose eq511 eq453
    | exact resolve eq453 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq656 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq67 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq67 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq67 X0 X0
       grind)
    | exact resolve eq12 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq664 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq67 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq667 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq656 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq670 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq667 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq667 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq667 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq667 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq674 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq670 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq670
    | (have j0 := eq670 X0 X1
       grind)
    | exact resolve eq670 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq786 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq52 X0 (M.op x X0) X0
       have i₂ := eq525 X0 x
       grind)
    | exact superpose eq525 eq52
    | exact resolve eq52 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq869 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
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
  have eq900 : (k (k (M.op x y) x) x) = (τ (k (k (σ (M.op x y)) (σ x)) (σ x))) := by
    first
    | exact superpose eq134 eq869
    | exact resolve eq869 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq1012 : (M.op y (M.op x y)) = (M.op (M.op x x) (M.op x y)) := by
    first
    | exact superpose eq512 eq560
    | exact resolve eq560 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq1123 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op y (M.op x y)) (M.op x x)) := by
    first
    | exact superpose eq1012 eq453
    | exact resolve eq453 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012
  have eq1126 : x = (M.op (M.op y (M.op x y)) (M.op x x)) := by
    first
    | (have i₁ := eq1123
       have i₂ := eq525 x x
       grind)
    | exact superpose eq525 eq1123
    | exact resolve eq1123 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123
  have eq1153 : (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) = (M.op x (M.op y (M.op x y))) := by
    first
    | exact superpose eq1126 eq453
    | exact resolve eq453 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq1157 : (M.op x y) = (M.op x (M.op y (M.op x y))) := by
    first
    | exact superpose eq212 eq1153
    | exact resolve eq1153 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq1153
  have eq1179 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq513 eq402
    | exact resolve eq402 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402 eq513
  have eq1418 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (M.op (σ x) (M.op (σ x) (σ x))) X0) (M.op (σ x) (M.op (σ x) (σ x))))) := by
    intro X0
    first
    | exact superpose eq1179 eq14
    | exact resolve eq14 eq1179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179
  have eq1429 : (M.op (σ x) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (M.op (σ x) (σ x))) (M.op (σ x) (M.op (σ x) (σ x))))) := by
    first
    | (have i₁ := eq1418 x
       have i₂ := eq453 (M.op sF2 (M.op sF2 sF2)) x
       grind)
    | exact superpose eq453 eq1418
    | exact resolve eq1418 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1418
  have eq1432 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq1429
       have i₂ := eq52 sF2 sF2 sF2
       grind)
    | exact superpose eq52 eq1429
    | exact resolve eq1429 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429
  have eq1434 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq1432
       have i₂ := eq525 sF2 sF2
       grind)
    | exact superpose eq525 eq1432
    | exact resolve eq1432 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1432
  have eq1997 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq525 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq786 X0
       grind)
    | exact superpose eq786 eq525
    | exact resolve eq525 eq786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq2003 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1997 X0
       have i₂ := eq52 X0 X0 X0
       grind)
    | exact superpose eq52 eq1997
    | exact resolve eq1997 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1997
  have eq2011 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2003 X0
       have i₂ := eq525 X0 X0
       grind)
    | exact superpose eq525 eq2003
    | exact resolve eq2003 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2003
  have eq7813 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op (M.op x y) x))) ∨ (σ (M.op (M.op x y) x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq377 eq664
    | (have j0 := eq664 x (M.op (M.op x y) x)
       grind)
    | exact resolve eq664 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7839 : (σ (M.op y (M.op x y))) ≠ (σ (M.op y (M.op x y))) ∨ (σ (M.op y (M.op x y))) = (M.op (σ (M.op y (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op y (M.op x y))) (σ (M.op y (M.op x y)))) := by
    first
    | exact superpose eq373 eq664
    | (have j0 := eq664 (M.op y (M.op x y)) (M.op x y)
       grind)
    | exact resolve eq664 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373 eq664
  have eq7939 : (σ (M.op y (M.op x y))) = (M.op (σ (M.op y (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op y (M.op x y))) (σ (M.op y (M.op x y)))) := by grind
  clear eq7839
  have eq7951 : (σ x) = (M.op (σ x) (σ (M.op (M.op x y) x))) ∨ (σ (M.op (M.op x y) x)) = (M.op (σ x) (σ x)) := by grind
  clear eq7813
  have eq8041 : (σ (M.op y (M.op x y))) = (M.op (σ (M.op y (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op y (M.op x y))) (σ (M.op y (M.op x y)))) := by
    first
    | exact superpose eq21 eq7939
    | exact resolve eq7939 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7939
  have eq8055 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ (σ (M.op (M.op x y) x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq511 eq7951
    | exact resolve eq7951 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7951
  have eq8140 : (σ (M.op x y)) = (M.op (σ (M.op y (M.op x y))) (σ (M.op y (M.op x y)))) ∨ (σ (M.op y (M.op x y))) = (M.op (σ (M.op y (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq8041
    | exact resolve eq8041 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8041
  have eq8154 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ (σ (M.op (M.op x y) x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8055
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8055
    | exact resolve eq8055 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8055
  have eq8243 : (σ (M.op (M.op x y) x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq8154
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8154
    | exact resolve eq8154 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8154
  have eq8329 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq511 eq8243
    | exact resolve eq8243 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8243
  have eq8556 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X1) X0)) ≠ (σ (M.op (M.op X0 X1) X0)) ∨ (σ (M.op (M.op X0 X1) X0)) = (M.op (σ (M.op (M.op X0 X1) X0)) (σ (M.op (M.op X0 X1) X0))) ∨ (σ X0) = (M.op (σ (M.op (M.op X0 X1) X0)) (σ (M.op (M.op X0 X1) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq674 X0 (M.op (M.op X0 X1) X0)
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq674
    | (have j0 := eq674 (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)
       grind)
    | exact resolve eq674 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq8563 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op (M.op x y) x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq377 eq674
    | (have j0 := eq674 x x
       grind)
    | exact resolve eq674 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq8698 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op (M.op x y) x)) = (M.op (σ x) (σ x)) := by grind
  clear eq8563
  have eq8705 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X1) X0)) = (M.op (σ (M.op (M.op X0 X1) X0)) (σ (M.op (M.op X0 X1) X0))) ∨ (σ X0) = (M.op (σ (M.op (M.op X0 X1) X0)) (σ (M.op (M.op X0 X1) X0))) := by
    intro X0 X1
    first
    | (have j0 := eq8556 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8556
  have eq8802 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op (M.op x y) x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8698
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8698
    | exact resolve eq8698 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8698
  have eq8804 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ (M.op (M.op X0 X1) X0)) (σ (M.op (M.op X0 X1) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8705 X0 X1
       have i₂ := eq453 X0 X1
       grind)
    | exact superpose eq453 eq8705
    | (have j0 := eq8705 X0 X1
       grind)
    | exact resolve eq8705 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8705
  have eq8896 : (σ (M.op (M.op x y) x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8802
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8802
    | exact resolve eq8802 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8802
  have eq8897 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq8804 X0 x
       have i₂ := eq453 X0 x
       grind)
    | exact superpose eq453 eq8804
    | (have j0 := eq8804 X0 x
       grind)
    | exact resolve eq8804 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8804
  have eq8987 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq511 eq8896
    | exact resolve eq8896 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511 eq8896
  have eq15217 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15225 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq15217
    | exact resolve eq15217 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15217
  have eq15236 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq15225
       have r₂ := eq28
       grind)
    | exact resolve eq15225 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15225
  have eq15238 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq15236
    | exact resolve eq15236 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15236
  have eq15244 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq15238 eq1434
    | exact resolve eq1434 eq15238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1434 eq15238
  have eq15284 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq15244
    | exact resolve eq15244 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15244
  have eq15285 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15284
  have eq15303 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2011 x
       have i₂ := eq15285
       grind)
    | exact superpose eq15285 eq2011
    | exact resolve eq2011 eq15285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15285
  have eq15336 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15303
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15303
    | exact resolve eq15303 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15303
  have eq15337 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15336
  have eq15347 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15337 eq28
    | exact resolve eq28 eq15337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15350 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15337 eq83
    | (have r₁ := eq83
       have r₂ := eq15337
       grind)
    | exact resolve eq83 eq15337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq15358 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15337 eq514
    | exact resolve eq514 eq15337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15368 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq15350
  have eq15435 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ x)) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15358 eq48
    | exact resolve eq48 eq15358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15358
  have eq17176 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ x)) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15337 eq15435
    | exact resolve eq15435 eq15337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15435
  have eq17199 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ x)) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq17176
  have eq17960 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq512 eq164
    | exact resolve eq164 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq17961 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq512 eq17960
    | exact resolve eq17960 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17960
  have eq18378 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15368 eq102
    | exact resolve eq102 eq15368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15368
  have eq18395 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq18378
  have eq21717 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq18395
  have eq23319 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21717 eq102
    | exact resolve eq102 eq21717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq21717
  have eq23346 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq23319
  have eq23356 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq23346
       have r₂ := eq15347
       grind)
    | exact resolve eq23346 eq15347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23346
  have eq23406 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  have eq23569 : (τ (σ x)) = (k (M.op x y) x) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23406 eq134
    | exact resolve eq134 eq23406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq23406
  have eq23595 : y = (M.op x x) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq23569
    | exact resolve eq23569 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23569
  have eq23770 : x = (M.op x y) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2011 x
       have i₂ := eq23595
       grind)
    | exact superpose eq23595 eq2011
    | exact resolve eq2011 eq23595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23595
  have eq23800 : x = (M.op x y) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23770
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq23770
    | exact resolve eq23770 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23770
  have eq23801 : x = (k (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq23800
  have eq23814 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23801 eq116
    | exact resolve eq116 eq23801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq23823 : x = (M.op x (M.op x y)) ∨ x = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23801 eq11
    | (have j0 := eq11 (M.op x y) x
       grind)
    | exact resolve eq11 eq23801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23830 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23801 eq674
    | (have j0 := eq674 x x
       grind)
    | exact resolve eq674 eq23801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23832 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq23830
  have eq23834 : (M.op x y) = (M.op x x) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq23823
  have eq23837 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23832
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq23832
    | exact resolve eq23832 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23832
  have eq23849 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23814
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq23814
    | exact resolve eq23814 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23814
  have eq23851 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23837
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq23837
    | exact resolve eq23837 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23837
  have eq23855 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq23851
    | exact resolve eq23851 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23851
  have eq23874 : (τ (k (σ x) (σ x))) = (k (k (M.op x y) x) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23849 eq900
    | exact resolve eq900 eq23849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900 eq23849
  have eq23892 : (k x x) = (k (k (M.op x y) x) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58 eq23874
    | exact resolve eq23874 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq23874
  have eq24434 : x = (M.op x (M.op x y)) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2011 x
       have i₂ := eq23834
       grind)
    | exact superpose eq23834 eq2011
    | exact resolve eq2011 eq23834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23834
  have eq24455 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq24434
  have eq24472 : x ≠ x ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24455 eq12
    | (have j0 := eq12 (M.op x y) x
       grind)
    | (have r₁ := eq12 (M.op x y) x
       have r₂ := eq24455
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq24455
       grind)
    | exact resolve eq12 eq24455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24455
  have eq24489 : (M.op x x) = (k (M.op x y) x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq24472
  have eq24520 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23855 eq17199
    | exact resolve eq17199 eq23855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17199
  have eq24545 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq24593 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq24520
  have eq24624 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq24593
    | exact resolve eq24593 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24593
  have eq24778 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15337 eq24624
    | exact resolve eq24624 eq15337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15337 eq24624
  have eq24798 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq24778
  have eq25107 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23855 eq24798
    | exact resolve eq24798 eq23855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23855 eq24798
  have eq25207 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq25107
  have eq25234 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq25207
       have r₂ := eq15347
       grind)
    | exact resolve eq25207 eq15347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25207
  have eq52582 : x = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24489 eq23801
    | exact resolve eq23801 eq24489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23801
  have eq52585 : (k x x) = (k (M.op x x) x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24489 eq23892
    | exact resolve eq23892 eq24489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23892 eq24489
  have eq52634 : (k x x) = (k (M.op x x) x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq52585
  have eq52637 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq52582
  have eq52650 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq52634
  have eq52726 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq525 x x
       have i₂ := eq52637
       grind)
    | exact superpose eq52637 eq525
    | exact resolve eq525 eq52637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52637
  have eq52744 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq512 eq52726
    | exact resolve eq52726 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52726
  have eq53129 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq525 x x
       have i₂ := eq52650
       grind)
    | exact superpose eq52650 eq525
    | exact resolve eq525 eq52650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52650
  have eq53146 : x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq512 eq53129
    | exact resolve eq53129 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53129
  have eq53559 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq52744 eq47
    | exact resolve eq47 eq52744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53598 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq53559
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53559
    | exact resolve eq53559 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53559
  have eq53605 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq512 eq53598
    | exact resolve eq53598 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53598
  have eq54032 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq674 x x
       have i₂ := eq53146
       grind)
    | exact superpose eq53146 eq674
    | (have j0 := eq674 x x
       grind)
    | exact resolve eq674 eq53146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq53146
  have eq54033 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by grind
  clear eq54032
  have eq54034 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by grind
  clear eq54033
  have eq54048 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq54034
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq54034
    | exact resolve eq54034 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54034
  have eq55408 : x = y ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq53605 eq52744
    | exact resolve eq52744 eq53605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52744 eq53605
  have eq55433 : x = (M.op x x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq55408
  have eq55454 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8987
       have i₂ := eq55433
       grind)
    | exact superpose eq55433 eq8987
    | exact resolve eq8987 eq55433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8987 eq55433
  have eq55503 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq55454
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq55454
    | exact resolve eq55454 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55454
  have eq55504 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq55503
  have eq56307 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq55504 eq25234
    | exact resolve eq25234 eq55504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25234 eq55504
  have eq56363 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq56307
  have eq56416 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq56363
       have r₂ := eq15347
       grind)
    | exact resolve eq56363 eq15347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56363
  have eq56451 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq56416 eq30
    | exact resolve eq30 eq56416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56416
  have eq56831 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq56451
    | exact resolve eq56451 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq56451
  have eq56832 : x = (M.op x y) ∨ x = y := by grind
  clear eq56831
  have eq98903 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq54048 eq23356
    | exact resolve eq23356 eq54048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23356 eq54048
  have eq98977 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by grind
  clear eq98903
  have eq99029 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have r₁ := eq98977
       have r₂ := eq15347
       grind)
    | exact resolve eq98977 eq15347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98977
  have eq102721 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq2011 x
       have i₂ := eq99029
       grind)
    | exact superpose eq99029 eq2011
    | exact resolve eq2011 eq99029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99029
  have eq102771 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq102721
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102721
    | exact resolve eq102721 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102721
  have eq102772 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq102771
  have eq102797 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq102772 eq1157
    | exact resolve eq1157 eq102772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq102799 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq102772 eq17961
    | exact resolve eq17961 eq102772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102806 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq102772 eq47
    | exact resolve eq47 eq102772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq102772
  have eq102833 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq102799
  have eq102851 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq102806
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102806
    | exact resolve eq102806 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102806
  have eq102852 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq102833
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq102833
    | exact resolve eq102833 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102833
  have eq102857 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq512 eq102851
    | exact resolve eq102851 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102851
  have eq102938 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq102797
       grind)
    | exact superpose eq102797 eq74
    | exact resolve eq74 eq102797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq102797
  have eq103001 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq102938
  have eq103016 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq103001
    | exact resolve eq103001 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103001
  have eq104754 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq102857 eq17961
    | exact resolve eq17961 eq102857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17961 eq102857
  have eq104797 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq104754
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq104754
    | exact resolve eq104754 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104754
  have eq104873 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq103016 eq24545
    | exact resolve eq24545 eq103016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24545 eq103016
  have eq104914 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq104873
  have eq104918 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq104914
       have r₂ := eq15347
       grind)
    | exact resolve eq104914 eq15347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15347 eq104914
  have eq136629 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104797 eq102852
    | exact resolve eq102852 eq104797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102852 eq104797
  have eq136657 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq136629
  have eq136675 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq136657 eq27
    | exact resolve eq27 eq136657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136657
  have eq140629 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq136675 eq104918
    | exact resolve eq104918 eq136675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104918 eq136675
  have eq140687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq140629
  have eq140762 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq140687
       have r₂ := eq28
       grind)
    | exact resolve eq140687 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140687
  have eq141047 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq140762
  have eq141052 : x = (M.op x y) := by
    first
    | (have r₁ := eq141047
       have r₂ := eq56832
       grind)
    | exact resolve eq141047 eq56832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56832 eq141047
  have eq141188 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq141052 eq21
    | exact resolve eq21 eq141052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq141193 : x ≠ x ∨ y = (M.op x x) ∨ (M.op x x) = (k y x) := by
    first
    | exact superpose eq141052 eq82
    | (have r₁ := eq82
       have r₂ := eq141052
       grind)
    | exact resolve eq82 eq141052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq141250 : (M.op x x) = (M.op y x) := by
    first
    | exact superpose eq141052 eq512
    | exact resolve eq512 eq141052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq141364 : (M.op x x) = (k y x) ∨ y = (M.op x x) := by grind
  clear eq141193
  have eq141495 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq141188
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq141188
    | exact resolve eq141188 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141188
  have eq141501 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq141495 eq27
    | exact resolve eq27 eq141495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169686 : (σ (M.op x y)) = (M.op (σ (M.op y x)) (σ (M.op y x))) ∨ (σ (M.op y (M.op x y))) = (M.op (σ (M.op y (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq141052 eq8140
    | exact resolve eq8140 eq141052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8140
  have eq169687 : (σ (M.op x y)) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ (σ (M.op y (M.op x y))) = (M.op (σ (M.op y (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq169686
       have i₂ := eq141250
       grind)
    | exact superpose eq141250 eq169686
    | exact resolve eq169686 eq141250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169686
  have eq169688 : (σ (M.op y x)) = (M.op (σ (M.op y x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | exact superpose eq141052 eq169687
    | exact resolve eq169687 eq141052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169687
  have eq169689 : (σ (M.op x y)) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq169688
       have i₂ := eq141250
       grind)
    | exact superpose eq141250 eq169688
    | exact resolve eq169688 eq141250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141250 eq169688
  have eq169724 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x y))) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2011 (σ (M.op x x))
       have i₂ := eq169689
       grind)
    | exact superpose eq169689 eq2011
    | exact resolve eq2011 eq169689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169689
  have eq169754 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by grind
  clear eq169724
  have eq172019 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq141364
       grind)
    | exact superpose eq141364 eq89
    | exact resolve eq89 eq141364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq141364
  have eq172085 : (σ (M.op x x)) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq141495 eq172019
    | exact resolve eq172019 eq141495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172019
  have eq198237 : (k (σ y) (σ (M.op x y))) = (M.op (k (σ y) (σ (M.op x y))) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq169754
       have i₂ := eq172085
       grind)
    | exact superpose eq172085 eq169754
    | exact resolve eq169754 eq172085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169754 eq172085
  have eq298222 : (M.op (σ (M.op x y)) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq198237
       have i₂ := eq11 sF3 sF1
       grind)
    | exact superpose eq11 eq198237
    | (have j1 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq198237 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198237
  have eq298283 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq298222
       have i₂ := eq453 sF1 sF3
       grind)
    | exact superpose eq453 eq298222
    | exact resolve eq298222 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453 eq298222
  have eq298289 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq141501 eq298283
    | exact resolve eq298283 eq141501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298283
  have eq298290 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq141501 eq298289
    | exact resolve eq298289 eq141501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298289
  have eq298291 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq298290
       have r₂ := eq28
       grind)
    | exact resolve eq298290 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298290
  have eq462514 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq298291 eq525
    | exact resolve eq525 eq298291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525 eq298291
  have eq462554 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq514 eq462514
    | exact resolve eq462514 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462514
  have eq462931 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq462554 eq2011
    | exact resolve eq2011 eq462554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462554
  have eq463006 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq141501 eq462931
    | exact resolve eq462931 eq141501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462931
  have eq463023 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq463006
       have r₂ := eq28
       grind)
    | exact resolve eq463006 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463006
  have eq463062 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq463023 eq48
    | exact resolve eq48 eq463023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq463126 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq141501 eq463062
    | exact resolve eq463062 eq141501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463062
  have eq463137 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq514 eq463126
    | exact resolve eq463126 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514 eq463126
  have eq463591 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq463137 eq463023
    | exact resolve eq463023 eq463137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463023 eq463137
  have eq463628 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq463591
  have eq463657 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq8329
       have i₂ := eq463628
       grind)
    | exact superpose eq463628 eq8329
    | exact resolve eq8329 eq463628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8329 eq463628
  have eq463800 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq463657
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq463657
    | exact resolve eq463657 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463657
  have eq463834 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq463800
    | exact resolve eq463800 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq463800
  have eq463854 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq141495 eq463834
    | exact resolve eq463834 eq141495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463834
  have eq463864 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq463854
       have r₂ := eq28
       grind)
    | exact resolve eq463854 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463854
  have eq463870 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq141495 eq463864
    | exact resolve eq463864 eq141495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463864
  have eq463875 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq463870
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq463870
    | exact resolve eq463870 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq463870
  have eq465074 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq463875 eq2011
    | exact resolve eq2011 eq463875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2011 eq463875
  have eq465146 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq141501 eq465074
    | exact resolve eq465074 eq141501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465074
  have eq465161 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq465146
       have r₂ := eq28
       grind)
    | exact resolve eq465146 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465146
  have eq465168 : y = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq465161 eq30
    | exact resolve eq30 eq465161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq465438 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq465161 eq141501
    | exact resolve eq141501 eq465161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141501 eq465161
  have eq465555 : y = (M.op x y) := by
    first
    | exact superpose eq31 eq465168
    | exact resolve eq465168 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq465168
  have eq465624 : x = y := by
    first
    | exact superpose eq141052 eq465555
    | exact resolve eq465555 eq141052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465555
  have eq465629 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq465624
       grind)
    | exact superpose eq465624 eq19
    | exact resolve eq19 eq465624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq465624
  have eq466125 : x = (M.op x x) := by
    first
    | exact superpose eq141052 eq465629
    | exact resolve eq465629 eq141052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141052 eq465629
  have eq466607 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8897 x
       have i₂ := eq466125
       grind)
    | exact superpose eq466125 eq8897
    | exact resolve eq8897 eq466125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8897 eq466125
  have eq466644 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq466607
  have eq466659 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq466644
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq466644
    | exact resolve eq466644 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq466644
  have eq466682 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq141495 eq466659
    | exact resolve eq466659 eq141495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141495 eq466659
  have eq466701 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq465438 eq466682
    | exact resolve eq466682 eq465438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465438 eq466682
  have eq466714 : False := by grind
  exact eq466714

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pyx_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq87 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq235 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq87 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq87 X0 X1
       grind)
    | exact resolve eq13 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq243 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq235 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq244 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq243 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq249 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq244 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq244
    | (have j0 := eq244 X0 X1
       grind)
    | exact resolve eq244 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq250 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq249 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq607 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq250 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq250
    | exact resolve eq250 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq615 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq250 x y
       grind)
    | exact superpose eq250 eq16
    | (have j1 := eq250 x y
       grind)
    | exact resolve eq16 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq636 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq607 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq607
    | (have j0 := eq607 X0 X1
       grind)
    | exact resolve eq607 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq607
  have eq642 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq636 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq636
    | exact resolve eq636 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq726 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq642 (τ X0) X1
       grind)
    | exact superpose eq642 eq18
    | (have j1 := eq642 (τ X0) X1
       grind)
    | exact resolve eq18 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq642
  have eq948 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq726 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq726
    | exact resolve eq726 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq997 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq948 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq948
    | (have j0 := eq948 X0 X1
       grind)
    | exact resolve eq948 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq1110 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq615
       have i₂ := eq997 x y
       grind)
    | exact superpose eq997 eq615
    | (have j1 := eq997 (σ x) (σ y)
       grind)
    | (have r₁ := eq615
       have r₂ := eq997 x y
       grind)
    | exact resolve eq615 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1111 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1110
  have eq1122 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1111
  have eq1140 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq615
       have i₂ := eq1122
       grind)
    | exact superpose eq1122 eq615
    | exact resolve eq615 eq1122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615 eq1122
  have eq1141 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1140
  have eq1142 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1141
  have eq1179 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1142
  have eq1199 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1179
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1179
    | exact resolve eq1179 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179
  have eq1204 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1199
       grind)
    | exact superpose eq1199 eq16
    | exact resolve eq16 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq1253 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1204
       have i₂ := eq997 x y
       grind)
    | exact superpose eq997 eq1204
    | (have j1 := eq997 x y
       grind)
    | (have r₁ := eq1204
       have r₂ := eq997 x y
       grind)
    | exact resolve eq1204 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq1254 : x = (M.op y y) := by grind
  clear eq1253
  have eq1258 : (M.op x y) = (k x y) := by grind
  clear eq1254
  have eq1320 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1204
       have i₂ := eq1258
       grind)
    | exact superpose eq1258 eq1204
    | exact resolve eq1204 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204 eq1258
  have eq1323 : False := by grind
  exact eq1323

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq271 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq271 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq274 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq272 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq272 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq272 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq287 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq274 (σ X0)
       grind)
    | exact superpose eq274 eq15
    | exact resolve eq15 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq287 X0
       have i₂ := eq274 X0
       grind)
    | exact superpose eq274 eq287
    | exact resolve eq287 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274 eq287
  have eq352 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq306 X0
       grind)
    | exact superpose eq306 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq306 X0
       grind)
    | exact superpose eq306 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq354 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq352 X0 X1
       have j1 := eq353 X0 X1
       grind)
    | (have r₁ := eq352 X0 X1
       have r₂ := eq353 X0 X1
       grind)
    | exact resolve eq352 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq353
  have eq538 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq354 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq354
    | exact resolve eq354 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq549 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq354 X1 (σ X0)
       grind)
    | exact superpose eq354 eq15
    | (have j1 := eq354 X1 (σ X0)
       grind)
    | exact resolve eq15 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq589 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq538 X1 (τ X0)
       grind)
    | exact superpose eq538 eq17
    | (have j1 := eq538 X1 (τ X0)
       grind)
    | exact resolve eq17 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq538
  have eq728 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq589 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq589
    | exact resolve eq589 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq754 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) X0
       have i₂ := eq589 X1 X0
       grind)
    | exact superpose eq589 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq589 X1 X0
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq589 X0 X1
       grind)
    | exact resolve eq13 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq761 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (k (τ X1) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq754 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq786 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq728 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq728
    | (have j0 := eq728 X0 X1
       grind)
    | exact resolve eq728 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq1015 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq549 x y
       grind)
    | exact superpose eq549 eq16
    | (have j1 := eq549 x y
       grind)
    | exact resolve eq16 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1036 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq549 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq66214 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (k (τ X0) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) X1)
       have i₂ := eq761 X1 X0
       grind)
    | exact superpose eq761 eq10
    | (have j1 := eq761 X1 X0
       grind)
    | exact resolve eq10 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq66305 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (k (τ X0) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq66214 X0 X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq66214
    | (have j0 := eq66214 X0 X1
       grind)
    | exact resolve eq66214 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq66214
  have eq66388 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq66305 X0 X1
       have j1 := eq12 (τ X0) X1
       grind)
    | (have r₁ := eq66305 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq66305 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66305
  have eq66710 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq66388 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq66388
    | exact resolve eq66388 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66388
  have eq67076 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1015
       have i₂ := eq66710 x y
       grind)
    | exact superpose eq66710 eq1015
    | (have j1 := eq66710 x y
       grind)
    | exact resolve eq1015 eq66710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015
  have eq67079 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq66710 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66710
  have eq67080 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq67076
  have eq67668 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1036 x y
       have i₂ := eq67080
       grind)
    | exact superpose eq67080 eq1036
    | (have j0 := eq1036 x y
       grind)
    | exact resolve eq1036 eq67080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036 eq67080
  have eq67703 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq67668
  have eq67704 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq67703
  have eq67712 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67704
       grind)
    | exact superpose eq67704 eq16
    | exact resolve eq16 eq67704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67759 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq67079 (σ x) (σ y)
       have i₂ := eq67704
       grind)
    | exact superpose eq67704 eq67079
    | (have j0 := eq67079 (σ x) (σ y)
       grind)
    | (have r₁ := eq67079 (σ x) (σ y)
       have r₂ := eq67704
       grind)
    | exact resolve eq67079 eq67704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67079 eq67704
  have eq67760 : (σ y) = (k (σ x) (σ y)) := by grind
  clear eq67759
  have eq67762 : (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq67760
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq67760
    | exact resolve eq67760 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67760
  have eq67861 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq786 x y
       have i₂ := eq67762
       grind)
    | exact superpose eq67762 eq786
    | (have j0 := eq786 x y
       grind)
    | exact resolve eq786 eq67762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786 eq67762
  have eq67982 : y = (M.op x y) := by
    first
    | (have r₁ := eq67861
       have r₂ := eq67712
       grind)
    | exact resolve eq67861 eq67712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67861
  have eq68050 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq67712
       have i₂ := eq67982
       grind)
    | exact superpose eq67982 eq67712
    | exact resolve eq67712 eq67982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67712 eq67982
  have eq68087 : False := by grind
  exact eq68087

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq68 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq70 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq85 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq70 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq86 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq85 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq105 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq86 (σ X0)
       grind)
    | exact superpose eq86 eq15
    | exact resolve eq15 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq105 X0
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq105
    | exact resolve eq105 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq105
  have eq133 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq112 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq112
    | (have j1 := eq14 (σ X0) (σ (M.op X0 X0))
       grind)
    | exact resolve eq112 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq157 X0 X1
       have j1 := eq133 X0 X1
       grind)
    | (have r₁ := eq157 X0 X1
       have r₂ := eq133 X0 X1
       grind)
    | (have r₁ := eq157 X0 (σ (M.op X0 X0))
       have r₂ := eq133 X0 X1
       grind)
    | (have r₁ := eq157 (M.op X0 X0) (σ X0)
       have r₂ := eq133 X0 X1
       grind)
    | exact resolve eq157 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq157
  have eq190 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq164 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq164
    | exact resolve eq164 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq164 X1 (σ X0)
       grind)
    | exact superpose eq164 eq15
    | (have j1 := eq164 (k X0 X1) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq202 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq190 (τ X1) X0
       grind)
    | exact superpose eq190 eq19
    | (have j1 := eq190 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq190
  have eq294 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq202 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq202
    | exact resolve eq202 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq317 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq294 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq294
    | (have j0 := eq294 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq294 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq1367 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq195 x y
       grind)
    | exact superpose eq195 eq16
    | (have j1 := eq195 x y
       grind)
    | exact resolve eq16 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq1391 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1367
       have i₂ := eq317 y x
       grind)
    | exact superpose eq317 eq1367
    | (have j1 := eq317 (σ x) (σ y)
       grind)
    | (have r₁ := eq1367
       have r₂ := eq317 y x
       grind)
    | (have r₁ := eq1367
       have r₂ := eq317 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1367
       have r₂ := eq317 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1367 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317 eq1367
  have eq1392 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1391
  have eq1394 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1392
       grind)
    | exact superpose eq1392 eq16
    | exact resolve eq16 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392
  have eq1395 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1394
       have r₂ := eq112 x
       grind)
    | exact resolve eq1394 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394
  have eq1396 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1395
       grind)
    | exact superpose eq1395 eq16
    | exact resolve eq16 eq1395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1397 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1395
       grind)
    | exact superpose eq1395 eq10
    | exact resolve eq10 eq1395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395
  have eq1442 : x = y := by
    first
    | (have i₁ := eq1397
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1397
    | exact resolve eq1397 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397
  have eq1443 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1396
       have i₂ := eq112 x
       grind)
    | exact superpose eq112 eq1396
    | exact resolve eq1396 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq1396
  have eq1444 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1443
       have i₂ := eq1442
       grind)
    | exact superpose eq1442 eq1443
    | exact resolve eq1443 eq1442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442 eq1443
  have eq1445 : False := by grind
  exact eq1445

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation1701 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq49 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq63 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (k (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ (M.op X0 X0)) (k (σ X0) X1)
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq98 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq103 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq98 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq98
    | (have j0 := eq98 X0 X1
       grind)
    | exact resolve eq98 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq357 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq103 x y
       grind)
    | exact superpose eq103 eq16
    | (have j1 := eq103 x y
       grind)
    | exact resolve eq16 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq103 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq963 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq97
    | exact resolve eq97 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq1002 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq963 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq963
    | (have j0 := eq963 X0 X1
       grind)
    | exact resolve eq963 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq1563 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq357
       have i₂ := eq1002 y x
       grind)
    | exact superpose eq1002 eq357
    | (have j1 := eq1002 y x
       grind)
    | (have r₁ := eq357
       have r₂ := eq1002 y x
       grind)
    | (have r₁ := eq357
       have r₂ := eq1002 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq357
       have r₂ := eq1002 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq357 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq1002
  have eq1564 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq1563
  have eq1729 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq367 (τ X0) (τ X1)
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq367
    | (have j0 := eq367 (τ X0) (τ X1)
       grind)
    | exact resolve eq367 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1758 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1729 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1729
    | (have j0 := eq1729 X0 X1
       grind)
    | exact resolve eq1729 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1729
  have eq1775 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1758 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq1758
    | (have j0 := eq1758 X0 X1
       grind)
    | exact resolve eq1758 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1758
  have eq1786 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1775 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1775
    | (have j0 := eq1775 X0 X1
       grind)
    | exact resolve eq1775 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775
  have eq1791 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1786 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1786
    | (have j0 := eq1786 X0 X1
       grind)
    | exact resolve eq1786 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786
  have eq1795 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1791 X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq1791
    | (have j0 := eq1791 X0 X1
       grind)
    | exact resolve eq1791 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1791
  have eq1798 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1795 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1795
    | (have j0 := eq1795 X0 X1
       grind)
    | exact resolve eq1795 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795
  have eq1799 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1798 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1798
    | (have j0 := eq1798 X0 X1
       grind)
    | exact resolve eq1798 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1798
  have eq15544 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1564
       grind)
    | exact superpose eq1564 eq16
    | exact resolve eq16 eq1564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564
  have eq15545 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq15544
       have r₂ := eq22 x
       grind)
    | exact resolve eq15544 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15544
  have eq15548 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq15545
       grind)
    | exact superpose eq15545 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq15545
       grind)
    | exact resolve eq13 eq15545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15545
  have eq15578 : x = y ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq15548
  have eq27540 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15578
       grind)
    | exact superpose eq15578 eq16
    | exact resolve eq16 eq15578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15578
  have eq27541 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq27540
       have r₂ := eq22 x
       grind)
    | exact resolve eq27540 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27540
  have eq27550 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq367 x y
       have i₂ := eq27541
       grind)
    | exact superpose eq27541 eq367
    | (have j0 := eq367 x y
       grind)
    | exact resolve eq367 eq27541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367 eq27541
  have eq27580 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq27550
  have eq27581 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq27580
  have eq27768 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27581
       grind)
    | exact superpose eq27581 eq16
    | exact resolve eq16 eq27581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27769 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq63 x (σ y)
       have i₂ := eq27581
       grind)
    | exact superpose eq27581 eq63
    | (have j0 := eq63 x (σ y)
       grind)
    | (have r₁ := eq63 x (σ y)
       have r₂ := eq27581
       grind)
    | exact resolve eq63 eq27581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq27581
  have eq27824 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq27769
  have eq27825 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq27824
  have eq27836 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq27825
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq27825
    | exact resolve eq27825 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27825
  have eq28337 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq27836
       grind)
    | exact superpose eq27836 eq10
    | exact resolve eq10 eq27836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27836
  have eq28536 : x = y ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq28337
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq28337
    | exact resolve eq28337 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28337
  have eq28538 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28536
       grind)
    | exact superpose eq28536 eq16
    | exact resolve eq16 eq28536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28536
  have eq28539 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq28538
       have r₂ := eq22 x
       grind)
    | exact resolve eq28538 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28538
  have eq29052 : (k x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq28539
       grind)
    | exact superpose eq28539 eq10
    | exact resolve eq10 eq28539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28539
  have eq29253 : (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq29052
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq29052
    | exact resolve eq29052 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29052
  have eq29274 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq1799 x y
       have i₂ := eq29253
       grind)
    | exact superpose eq29253 eq1799
    | (have j0 := eq1799 x y
       grind)
    | (have r₁ := eq1799 x y
       have r₂ := eq29253
       grind)
    | exact resolve eq1799 eq29253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1799 eq29253
  have eq29295 : x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq29274
  have eq29781 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29295
       grind)
    | exact superpose eq29295 eq16
    | exact resolve eq16 eq29295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29295
  have eq29784 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq29781
       have r₂ := eq22 x
       grind)
    | exact resolve eq29781 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29781
  have eq29785 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq27768
       have i₂ := eq29784
       grind)
    | exact superpose eq29784 eq27768
    | exact resolve eq27768 eq29784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27768
  have eq29823 : (σ x) = (σ y) := by grind
  clear eq29785
  have eq30222 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29823
       grind)
    | exact superpose eq29823 eq16
    | exact resolve eq16 eq29823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29823
  have eq30424 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq30222
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq30222
    | exact resolve eq30222 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq30222
  have eq30425 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq30424
       have i₂ := eq29784
       grind)
    | exact superpose eq29784 eq30424
    | exact resolve eq30424 eq29784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29784 eq30424
  have eq30426 : False := by grind
  exact eq30426

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation1701 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq97 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq284 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq97 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq97 X0 X1
       grind)
    | exact superpose eq97 eq13
    | (have j0 := eq13 (k (σ X0) (σ X1)) (M.op (σ X0) (σ X1))
       have j1 := eq97 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq97 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq97 X0 X1
       grind)
    | exact resolve eq13 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq288 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq284 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq289 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq288 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq296 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq289 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq289
    | (have j0 := eq289 X0 X1
       grind)
    | exact resolve eq289 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq297 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq296 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq407 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq297 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq297
    | exact resolve eq297 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq297 x y
       grind)
    | exact superpose eq297 eq16
    | (have j1 := eq297 x y
       grind)
    | exact resolve eq16 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq435 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq407 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq407
    | (have j0 := eq407 X0 X1
       grind)
    | exact resolve eq407 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq407
  have eq468 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq435 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq435
    | exact resolve eq435 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq566 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq413
       have i₂ := eq468 x y
       grind)
    | exact superpose eq468 eq413
    | (have j1 := eq468 (σ x) (σ y)
       grind)
    | (have r₁ := eq413
       have r₂ := eq468 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq413
       have r₂ := eq468 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq413 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413 eq468
  have eq569 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq566
  have eq616 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq569
       grind)
    | exact superpose eq569 eq10
    | exact resolve eq10 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq651 : x = y ∨ x = y := by
    first
    | (have i₁ := eq616
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq616
    | exact resolve eq616 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq652 : x = y := by grind
  clear eq651
  have eq654 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq652
       grind)
    | exact superpose eq652 eq16
    | exact resolve eq16 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq655 : False := by grind
  exact eq655

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxx_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
    intro X0 X1 X2
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
  have eq54 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) := by
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
  have eq74 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq76 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq45
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
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
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq101
    | exact resolve eq101 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq107
    | exact resolve eq107 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq388 : ∀ X0 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    grind
  have eq396 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq388 X0
       have i₂ := eq54 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq54 eq388
    | exact resolve eq388 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq388
  have eq464 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq74 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq12518 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq108 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12519 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq12518
    | exact resolve eq12518 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12518
  have eq12530 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq12519
       have r₂ := eq29
       grind)
    | exact resolve eq12519 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12519
  have eq12533 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq12530
  have eq12582 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq12533
    | exact resolve eq12533 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12533
  have eq12588 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq12582 eq108
    | exact resolve eq108 eq12582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq12582
  have eq12599 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq12588
  have eq12602 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq12599
       have r₂ := eq29
       grind)
    | exact resolve eq12599 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12599
  have eq12720 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq12602
  have eq12770 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12720
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq12720
    | exact resolve eq12720 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12720
  have eq12773 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq12770
       grind)
    | exact superpose eq12770 eq46
    | exact resolve eq46 eq12770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq12770
  have eq12793 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22 eq12773
    | exact resolve eq12773 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12773
  have eq12966 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12793 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq12793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12967 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq12966
  have eq12971 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28 eq12967
    | exact resolve eq12967 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12967
  have eq12982 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq12971
       have r₂ := eq29
       grind)
    | exact resolve eq12971 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12971
  have eq13150 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq12982
  have eq13199 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq13150
    | exact resolve eq13150 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13150
  have eq13213 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13199 eq12793
    | exact resolve eq12793 eq13199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12793 eq13199
  have eq13218 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq13213
  have eq13223 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq13218
       have r₂ := eq29
       grind)
    | exact resolve eq13218 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13218
  have eq13340 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq13223 eq31
    | exact resolve eq31 eq13223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq13223
  have eq13456 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq13340
    | exact resolve eq13340 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq13340
  have eq13457 : x = y := by grind
  clear eq13456
  have eq13458 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq13457
       grind)
    | exact superpose eq13457 eq20
    | exact resolve eq20 eq13457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq13459 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq13457
       grind)
    | exact superpose eq13457 eq26
    | exact resolve eq26 eq13457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq13457
  have eq13561 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq13459
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13459
    | exact resolve eq13459 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13459
  have eq13562 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq13561 eq28
    | exact resolve eq28 eq13561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq13561
  have eq13773 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq13458
       grind)
    | exact superpose eq13458 eq76
    | exact resolve eq76 eq13458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq13791 : (M.op x y) = (k (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq396 x
       have i₂ := eq13458
       grind)
    | exact superpose eq13458 eq396
    | exact resolve eq396 eq13458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13817 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22 eq13773
    | exact resolve eq13773 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13773
  have eq13835 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq13562 eq396
    | exact resolve eq396 eq13562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq15381 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq15394 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13562 eq15381
    | exact resolve eq15381 eq13562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15381
  have eq15406 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15394
       have r₂ := eq29
       grind)
    | exact resolve eq15394 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15394
  have eq15411 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13562 eq15406
    | exact resolve eq15406 eq13562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15406
  have eq15626 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15411 eq29
    | exact resolve eq29 eq15411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15641 : (σ x) = (k (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15411 eq13835
    | exact resolve eq13835 eq15411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13835
  have eq15647 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13562 eq15641
    | exact resolve eq15641 eq13562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15641
  have eq15832 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15411 eq15647
    | exact resolve eq15647 eq15411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15411 eq15647
  have eq15837 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq15832
  have eq15886 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15837 eq13817
    | exact resolve eq13817 eq15837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13817 eq15837
  have eq15901 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq15886
  have eq15908 : x = (M.op x y) := by
    first
    | (have r₁ := eq15901
       have r₂ := eq15626
       grind)
    | exact resolve eq15901 eq15626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15626 eq15901
  have eq15927 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq15908 eq22
    | exact resolve eq22 eq15908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq15992 : x = (k x (M.op x x)) := by
    first
    | exact superpose eq15908 eq13791
    | exact resolve eq13791 eq15908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13791
  have eq16005 : x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq15992
       have i₂ := eq13458
       grind)
    | exact superpose eq13458 eq15992
    | exact resolve eq15992 eq13458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13458 eq15992
  have eq16070 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq15927
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15927
    | exact resolve eq15927 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15927
  have eq16074 : x = (k x x) := by
    first
    | exact superpose eq15908 eq16005
    | exact resolve eq16005 eq15908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15908 eq16005
  have eq16396 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq464 x
       have i₂ := eq16074
       grind)
    | exact superpose eq16074 eq464
    | (have j0 := eq464 x
       grind)
    | exact resolve eq464 eq16074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464 eq16074
  have eq16400 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq16396
  have eq16406 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16400
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16400
    | exact resolve eq16400 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq16400
  have eq16424 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13562 eq16406
    | exact resolve eq16406 eq13562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13562 eq16406
  have eq16440 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16070 eq16424
    | exact resolve eq16424 eq16070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16070 eq16424
  have eq16455 : False := by grind
  exact eq16455
