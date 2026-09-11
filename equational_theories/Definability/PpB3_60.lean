import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4069`: `x ◇ x = ((x ◇ x) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_x_x_x_pyx_Equation4069 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4069 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4069.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X2) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq13 X0 (k (M.op X0 X0) X1)
       grind)
    | exact resolve eq12 eq13
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
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
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
  clear eq45
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
  have eq125 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq51
    | (have j0 := eq51 (M.op x y)
       grind)
    | exact resolve eq51 eq20
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
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : y ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq177 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq38 (M.op sF0 sF0)
       have i₂ := eq175 sF0
       grind)
    | exact superpose eq175 eq38
    | exact resolve eq38 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq180
    | exact resolve eq180 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq191 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq91 (M.op sF2 sF2)
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq91
    | exact resolve eq91 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq30 eq191
    | exact resolve eq191 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq209 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq108 (M.op sF3 sF3)
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq108
    | exact resolve eq108 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq220 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq209
    | exact resolve eq209 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq227 : (τ (σ (M.op x y))) = (k (M.op x y) (τ (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | (have i₁ := eq125 (M.op sF1 sF1)
       have i₂ := eq175 sF1
       grind)
    | exact superpose eq175 eq125
    | exact resolve eq125 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq238 : (M.op x y) = (k (M.op x y) (τ (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | exact superpose eq29 eq227
    | exact resolve eq227 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq399 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq39
  have eq553 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq399 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq175 (σ X0)
       grind)
    | exact superpose eq175 eq399
    | exact resolve eq399 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq582 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq553 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq553
    | exact resolve eq553 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq691 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq16 (M.op X0 X0) x X2
       have i₂ := eq16 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq726 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X1 (M.op (M.op X0 X0) X2)) ∨ (M.op X0 X0) = X1 ∨ (M.op (M.op X0 X0) X2) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X2 (M.op (M.op X0 X0) X1)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq11
    | (have j0 := eq11 X0 (k X1 (M.op (M.op X0 X0) X2))
       grind)
    | exact resolve eq11 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq727 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq728 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq729 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X1) X2) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq746 : (M.op x y) = (k (M.op x y) (τ (k (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq238
       have i₂ := eq11 sF1 sF1
       grind)
    | exact superpose eq11 eq238
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq238 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq750 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq751 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq752 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq751 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq755 : (M.op x y) = (k (M.op x y) (τ (k (σ (M.op x y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq746
  have eq768 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X1) X2) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq729 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq772 : (M.op x y) = (k (M.op x y) (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq134 eq755
    | exact resolve eq755 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq805 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq752 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq752
    | (have j0 := eq752 (σ X0)
       grind)
    | exact resolve eq752 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq869 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq691 X0 X1
       have i₂ := eq691 X0 X2
       grind)
    | (have i₁ := eq691 X0 X2
       have i₂ := eq691 X0 (M.op X0 X0)
       grind)
    | exact superpose eq691 eq691
    | exact resolve eq691 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq879 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op X0 X0)
       have i₂ := eq691 X0 X1
       grind)
    | (have i₁ := eq175 (M.op X0 X0)
       have i₂ := eq691 X0 (M.op X0 X0)
       grind)
    | exact superpose eq691 eq175
    | exact resolve eq175 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq881 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 x (M.op X0 X0)
       have i₂ := eq691 X0 x
       grind)
    | (have i₁ := eq11 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq691 X0 x
       grind)
    | exact superpose eq691 eq11
    | (have j0 := eq11 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact resolve eq11 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq882 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq691 X0 X1
       grind)
    | (have i₁ := eq28 x (M.op X0 X0)
       have i₂ := eq691 X0 x
       grind)
    | exact superpose eq691 eq28
    | (have j0 := eq28 (M.op X0 X0) (M.op X0 X0)
       grind)
    | (have r₁ := eq28 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
       have r₂ := eq691 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq28 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq883 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq881 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq934 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq727
       grind)
    | exact superpose eq727 eq40
    | exact resolve eq40 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq935 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq934
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq934
    | exact resolve eq934 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq937 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq935
    | exact resolve eq935 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq960 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq937 eq728
    | exact resolve eq728 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq967 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq960
       have r₂ := eq27
       grind)
    | exact resolve eq960 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq972 : y = (k y (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq967 eq220
    | exact resolve eq220 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq984 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq972
    | exact resolve eq972 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq986 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq984
       have r₂ := eq176
       grind)
    | exact resolve eq984 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq984
  have eq987 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq986
       have r₂ := eq13 y x
       grind)
    | exact resolve eq986 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq991 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq987
       grind)
    | exact superpose eq987 eq40
    | exact resolve eq40 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq994 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq991
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq991
    | exact resolve eq991 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq996 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq994
       have r₂ := eq177
       grind)
    | exact resolve eq994 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq994
  have eq1001 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq996 eq728
    | exact resolve eq728 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq1004 : (τ (σ y)) = (k (τ (σ y)) x) := by
    first
    | exact superpose eq996 eq142
    | exact resolve eq142 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq996
  have eq1005 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1001
  have eq1007 : y = (k y x) := by
    first
    | exact superpose eq32 eq1004
    | exact resolve eq1004 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq1012 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq727
       have i₂ := eq1007
       grind)
    | exact superpose eq1007 eq727
    | exact resolve eq727 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727 eq1007
  have eq1015 : x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq1012
  have eq1020 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1005
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq1005
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq1005 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1022 : ∀ X0 : G, (σ x) = (k (σ x) (M.op (σ x) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1005 eq879
    | exact resolve eq879 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1023 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1005 eq869
    | exact resolve eq869 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1024 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1005 eq691
    | exact resolve eq691 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1025 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1005 eq16
    | exact resolve eq16 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1028 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1005 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1030 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1028
  have eq1031 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1020
  have eq1033 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1030 eq1031
    | exact resolve eq1031 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031
  have eq1034 : x = (k y y) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1015
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq1015
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq1015 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1037 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq869 y X1 x
       have i₂ := eq1015
       grind)
    | exact superpose eq1015 eq869
    | exact resolve eq869 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1038 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq691 y x
       have i₂ := eq1015
       grind)
    | exact superpose eq1015 eq691
    | exact resolve eq691 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1039 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y X1 x
       have i₂ := eq1015
       grind)
    | exact superpose eq1015 eq16
    | exact resolve eq16 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1042 : x = (k y y) ∨ x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq1015
       grind)
    | exact superpose eq1015 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1043 : x ≠ y ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq1015
       grind)
    | exact superpose eq1015 eq28
    | (have j0 := eq28 y y
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq1015
       grind)
    | exact resolve eq28 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015
  have eq1044 : x = (k y y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq1042
  have eq1045 : x = (k y y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq1034
  have eq1047 : x = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1044 eq1045
    | exact resolve eq1045 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1050 : ∀ X0 : G, (τ (σ x)) = (k x (τ (M.op (σ x) X0))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1022 eq91
    | exact resolve eq91 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq1022
  have eq1051 : ∀ X0 : G, x = (k x (τ (M.op (σ x) X0))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30 eq1050
    | exact resolve eq1050 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq1066 : ∀ X0 X1 : G, (k X0 (σ x)) = (M.op (σ x) X1) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) X0) = X0 ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq1023 X0 X0
       have i₂ := eq11 X0 sF2
       grind)
    | exact superpose eq11 eq1023
    | (have j1 := eq11 X0 (σ x)
       grind)
    | exact resolve eq1023 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1078 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1023 eq26
    | (have j1 := eq1023 (σ y) X0
       grind)
    | exact resolve eq26 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq1103 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) X0) = X0 ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq1078 eq1066
    | (have j0 := eq1066 X0 (σ y)
       grind)
    | exact resolve eq1066 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066
  have eq1114 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1078 eq879
    | exact resolve eq879 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq1115 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (σ y)) X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1078 eq869
    | exact resolve eq869 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1116 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1078 eq691
    | exact resolve eq691 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq1117 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1078 eq16
    | exact resolve eq16 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1119 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ X0 ∨ (σ x) = (k (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1078 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq1078 (σ x)
       grind)
    | exact resolve eq13 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1120 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 (σ x)) ∨ (M.op (σ x) (σ y)) = X0 ∨ (M.op X0 X0) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1078 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1149 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1024 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1162 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1149 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149
  have eq1175 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1078 eq1162
    | (have j0 := eq1162 (σ y)
       grind)
    | exact resolve eq1162 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq1185 : ∀ X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) X1) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq1078 eq1025
    | (have j0 := eq1025 (σ y) X1
       grind)
    | exact resolve eq1025 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025
  have eq1212 : ∀ X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have j0 := eq1185 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq1357 : ∀ X0 X1 : G, (k X0 x) = (M.op x X1) ∨ y = (M.op x y) ∨ (M.op x X0) = X0 ∨ (M.op X0 X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq1037 X1 X0
       have i₂ := eq11 X0 x
       grind)
    | exact superpose eq11 eq1037
    | (have j1 := eq11 X0 x
       grind)
    | exact resolve eq1037 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1370 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq1037 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq1037 X0 y
       grind)
    | exact superpose eq1037 eq18
    | (have j1 := eq1037 y X0
       grind)
    | exact resolve eq18 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037
  have eq1398 : ∀ X0 : G, (M.op x y) = (k X0 x) ∨ y = (M.op x y) ∨ (M.op x X0) = X0 ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq1370 eq1357
    | (have j0 := eq1357 X0 y
       grind)
    | exact resolve eq1357 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357
  have eq1409 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ x = (k x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq1370 x
       grind)
    | exact superpose eq1370 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq1370 x
       grind)
    | exact resolve eq13 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1462 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x X0) ∨ x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11 x x
       have i₂ := eq1038 X0
       grind)
    | (have i₁ := eq11 X0 x
       have i₂ := eq1038 X0
       grind)
    | exact superpose eq1038 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038
  have eq1475 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1462 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1462
  have eq1488 : ∀ X0 : G, (M.op x y) = (k x x) ∨ x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1370 eq1475
    | (have j0 := eq1475 y
       grind)
    | exact resolve eq1475 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475
  have eq1496 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1370 eq1488
    | (have j0 := eq1488 y
       grind)
    | exact resolve eq1488 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488
  have eq1501 : ∀ X1 : G, x = (M.op (M.op x y) X1) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq1039 x X1
       have i₂ := eq1370 x
       grind)
    | (have i₁ := eq1039 y X1
       have i₂ := eq1370 x
       grind)
    | exact superpose eq1370 eq1039
    | (have j0 := eq1039 y X1
       grind)
    | exact resolve eq1039 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1510 : ∀ X0 X1 : G, x = (k X0 (M.op x X1)) ∨ y = (M.op x y) ∨ (M.op (M.op x X1) X0) = X0 ∨ (M.op X0 X0) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1039 X1 X0
       have i₂ := eq11 X0 (M.op x X1)
       grind)
    | exact superpose eq11 eq1039
    | (have j1 := eq11 X0 (M.op x X1)
       grind)
    | exact resolve eq1039 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1529 : ∀ X1 : G, x = (M.op (M.op x y) X1) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have j0 := eq1501 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501
  have eq1535 : ∀ X0 X1 : G, x = (k X0 (M.op x y)) ∨ y = (M.op x y) ∨ (M.op (M.op x X1) X0) = X0 ∨ (M.op X0 X0) = (M.op x X1) := by
    intro X0 X1
    first
    | exact superpose eq1370 eq1510
    | (have j0 := eq1510 X0 X1
       grind)
    | exact resolve eq1510 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1510
  have eq1538 : ∀ X0 X1 : G, x = (k X0 (M.op x y)) ∨ y = (M.op x y) ∨ (M.op (M.op x y) X0) = X0 ∨ (M.op X0 X0) = (M.op x X1) := by
    intro X0 X1
    first
    | exact superpose eq1370 eq1535
    | (have j0 := eq1535 X0 y
       grind)
    | exact resolve eq1535 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535
  have eq1540 : ∀ X0 : G, x = (k X0 (M.op x y)) ∨ y = (M.op x y) ∨ (M.op (M.op x y) X0) = X0 ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1370 eq1538
    | (have j0 := eq1538 X0 y
       grind)
    | exact resolve eq1538 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538
  have eq1581 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) ≠ X1 ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1115 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) X1
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X1)
       have r₂ := eq1115 (M.op (σ x) (σ y)) X1
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)
       have r₂ := eq1115 X0 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq13 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1588 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (k X1 (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (σ y)) X0) = X1 ∨ (M.op (σ x) (σ y)) = (M.op X1 X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1115 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1600 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X1 X1) ∨ (M.op (M.op (σ x) (σ y)) X0) = X1 ∨ (σ x) = (k X1 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1212 eq1588
    | (have j0 := eq1588 X0 X1
       grind)
    | exact resolve eq1588 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1588
  have eq1642 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1116 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1644 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1642 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1642
  have eq1661 : ∀ X0 : G, (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1212 eq1644
    | (have j0 := eq1644 X0
       grind)
    | exact resolve eq1644 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1644
  have eq1670 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1212 eq1661
    | exact resolve eq1661 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1661
  have eq1865 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1030 eq116
    | exact resolve eq116 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030
  have eq1874 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq1865
    | exact resolve eq1865 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1865
  have eq1880 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq1044
       grind)
    | exact superpose eq1044 eq41
    | exact resolve eq41 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1885 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1880
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1880
    | exact resolve eq1880 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1880
  have eq1887 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1885
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1885
    | exact resolve eq1885 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885
  have eq1947 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq768 y X1 x
       have i₂ := eq1874
       grind)
    | exact superpose eq1874 eq768
    | (have j0 := eq768 y X1 x
       grind)
    | exact resolve eq768 eq1874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1954 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1039 eq1947
    | (have j0 := eq1947 X0 X1
       have j1 := eq1039 X0 X1
       grind)
    | exact resolve eq1947 eq1039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039 eq1947
  have eq2050 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1496
       grind)
    | exact superpose eq1496 eq40
    | exact resolve eq40 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2057 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2050
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2050
    | exact resolve eq2050 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2050
  have eq2059 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq2057
    | exact resolve eq2057 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057
  have eq2066 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1887 eq768
    | (have j0 := eq768 (σ y) X1 x
       grind)
    | exact resolve eq768 eq1887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq2115 : (τ (σ x)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1033 eq116
    | exact resolve eq116 eq1033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033
  have eq2128 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq2115
    | exact resolve eq2115 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2115
  have eq2133 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq1047
       grind)
    | exact superpose eq1047 eq41
    | exact resolve eq41 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1047
  have eq2142 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2133
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2133
    | exact resolve eq2133 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2133
  have eq2144 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2142
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2142
    | exact resolve eq2142 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2142
  have eq2146 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1370 eq2144
    | exact resolve eq2144 eq1370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370 eq2144
  have eq2149 : (τ (σ x)) = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2146 eq116
    | exact resolve eq116 eq2146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq2146
  have eq2160 : x = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq2149
    | exact resolve eq2149 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2149
  have eq2206 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1175 eq2059
    | (have j1 := eq1175 X0
       grind)
    | exact resolve eq2059 eq1175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175
  have eq2219 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2206 X0
       grind)
    | (have r₁ := eq2206 X0
       have r₂ := eq27
       grind)
    | exact resolve eq2206 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2206
  have eq2245 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq2128 eq28
    | (have j0 := eq28 (σ x) (σ x)
       grind)
    | (have r₁ := eq28 (σ x) (σ x)
       have r₂ := eq2128
       grind)
    | (have r₁ := eq28 (σ y) (σ x)
       have r₂ := eq2128
       grind)
    | exact resolve eq28 eq2128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2128
  have eq2246 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by grind
  clear eq2245
  have eq2396 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ x) (σ (M.op (M.op X0 X0) X1))) ∨ (M.op X0 X0) = x ∨ (M.op (M.op X0 X0) X1) = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq36 (M.op (M.op X0 X0) X1)
       have i₂ := eq726 X0 x X1
       grind)
    | exact superpose eq726 eq36
    | (have j1 := eq726 X0 x X1
       grind)
    | exact resolve eq36 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq2799 : x = (k x (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2219 eq1051
    | exact resolve eq1051 eq2219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051 eq2219
  have eq2818 : x = (k x (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2799
  have eq2834 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq2818
    | exact resolve eq2818 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2818
  have eq2837 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq1409 x
       grind)
    | (have r₁ := eq2834
       have r₂ := eq1409 y
       grind)
    | (have r₁ := eq2834
       have r₂ := eq1409 x
       grind)
    | exact resolve eq2834 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2834
  have eq2842 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1496
       have i₂ := eq2837
       grind)
    | exact superpose eq2837 eq1496
    | exact resolve eq1496 eq2837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2845 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq2837
       grind)
    | exact superpose eq2837 eq40
    | exact resolve eq40 eq2837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2837
  have eq2854 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2842
  have eq2862 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2845
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2845
    | exact resolve eq2845 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2845
  have eq2866 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2854 eq27
    | exact resolve eq27 eq2854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2881 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2862 eq750
    | (have j0 := eq750 (σ x) (σ x)
       grind)
    | (have r₁ := eq750 (σ x) (σ x)
       have r₂ := eq2862
       grind)
    | exact resolve eq750 eq2862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2882 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2881
  have eq2883 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2882
  have eq2905 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2883 eq1078
    | exact resolve eq1078 eq2883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2883
  have eq2922 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2905
  have eq2944 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq5427 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1103 eq752
    | (have j0 := eq752 (σ x)
       have j1 := eq1103 (σ x)
       grind)
    | exact resolve eq752 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq5463 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5427
  have eq5633 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq1398 x
       grind)
    | exact superpose eq1398 eq36
    | (have j1 := eq1398 x
       grind)
    | exact resolve eq36 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1398
  have eq5644 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq5633
  have eq5662 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5644
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5644
    | exact resolve eq5644 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5644
  have eq5669 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq5662
    | exact resolve eq5662 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5662
  have eq5673 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2059 eq5669
    | exact resolve eq5669 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5669
  have eq5682 : (τ (σ (M.op x y))) = (k x x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5673 eq98
    | exact resolve eq98 eq5673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq5673
  have eq5711 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq29 eq5682
    | exact resolve eq5682 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5682
  have eq5742 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1540 eq752
    | (have j0 := eq752 (M.op x y)
       have j1 := eq1540 (M.op x y)
       grind)
    | exact resolve eq752 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq5751 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1540 eq38
    | (have j1 := eq1540 (M.op x y)
       grind)
    | exact resolve eq38 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1540
  have eq5755 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq5751
  have eq5760 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq5742
  have eq5769 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq5755
    | exact resolve eq5755 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5755
  have eq5776 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq5769
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5769
    | exact resolve eq5769 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5769
  have eq5783 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5776 eq134
    | exact resolve eq134 eq5776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq5776
  have eq5803 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq30 eq5783
    | exact resolve eq5783 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5783
  have eq5815 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5803 eq1529
    | exact resolve eq1529 eq5803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5828 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5803 eq28
    | (have j0 := eq28 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq28 (M.op x y) (M.op x y)
       have r₂ := eq5803
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq5803
       grind)
    | exact resolve eq28 eq5803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5803
  have eq5829 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq5828
  have eq5832 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5815
  have eq5900 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq5829
  have eq5907 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq5900
       have r₂ := eq5832
       grind)
    | exact resolve eq5900 eq5832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5832 eq5900
  have eq5918 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5907 eq42
    | exact resolve eq42 eq5907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5907
  have eq5930 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq5918
    | exact resolve eq5918 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5918
  have eq5932 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5930
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5930
    | exact resolve eq5930 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5930
  have eq8236 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1954 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1954
    | (have j0 := eq1954 y X0
       grind)
    | exact resolve eq1954 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1954
  have eq8269 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq8236 eq181
    | (have j1 := eq8236 X0
       grind)
    | exact resolve eq181 eq8236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8236
  have eq8291 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq8269
    | (have j0 := eq8269 X0
       grind)
    | exact resolve eq8269 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8269
  have eq8343 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq8291 eq750
    | (have j0 := eq750 (σ (M.op x y)) (σ (M.op x y))
       have j1 := eq8291 X0
       grind)
    | (have r₁ := eq750 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq8291 X0
       grind)
    | exact resolve eq750 eq8291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8291
  have eq8344 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq8343 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8343
  have eq8345 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq8344 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8344
  have eq8985 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1114 sF4
       have i₂ := eq1600 X0 sF4
       grind)
    | exact superpose eq1600 eq1114
    | (have j1 := eq1600 X0 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1114 eq1600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114 eq1600
  have eq9002 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq8985 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8985
  have eq9093 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have j1 := eq1581 x (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9002 x
       have r₂ := eq1581 x (M.op (σ x) (σ y))
       grind)
    | exact resolve eq9002 eq1581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1581 eq9002
  have eq9210 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1670 eq9093
    | exact resolve eq9093 eq1670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1670 eq9093
  have eq10935 : (σ (σ x)) ≠ (σ (σ x)) ∨ (σ (σ x)) = (M.op (σ (σ x)) (σ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq2246 eq805
    | (have j0 := eq805 (σ x)
       grind)
    | exact resolve eq805 eq2246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2246
  have eq10937 : (σ (σ x)) ≠ (σ (σ x)) ∨ (σ (σ x)) = (M.op (σ (σ x)) (σ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2862 eq805
    | (have j0 := eq805 (σ x)
       grind)
    | exact resolve eq805 eq2862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2862
  have eq10964 : (σ (σ x)) = (M.op (σ (σ x)) (σ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10937
  have eq10966 : (σ (σ x)) = (M.op (σ (σ x)) (σ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by grind
  clear eq10935
  have eq10993 : (σ (σ x)) = (M.op (σ (σ x)) (σ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq10964 eq10966
    | exact resolve eq10966 eq10964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10964 eq10966
  have eq11506 : (σ x) = (k (σ x) (τ (σ (σ x)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq10993 eq582
    | exact resolve eq582 eq10993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq10993
  have eq11538 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq11506
       have i₂ := eq15 sF2
       grind)
    | exact superpose eq15 eq11506
    | exact resolve eq11506 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11506
  have eq11566 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq11538 eq750
    | (have j0 := eq750 (σ x) (σ x)
       grind)
    | (have r₁ := eq750 (σ x) (σ x)
       have r₂ := eq11538
       grind)
    | exact resolve eq750 eq11538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11538
  have eq11567 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq11566
  have eq11568 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq11567
  have eq11650 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq11568 eq1078
    | exact resolve eq1078 eq11568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11568
  have eq11686 : x = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11650
  have eq11721 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11686 eq772
    | exact resolve eq772 eq11686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq11728 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11686 eq42
    | exact resolve eq42 eq11686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq11686
  have eq11747 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq11728
    | exact resolve eq11728 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11728
  have eq11750 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11747
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11747
    | exact resolve eq11747 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11747
  have eq12164 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq11721
       have i₂ := eq11 sF1 sF1
       grind)
    | exact superpose eq11 eq11721
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11721 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12187 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11721 eq28
    | (have j0 := eq28 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq28 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq11721
       grind)
    | (have r₁ := eq28 (σ y) (σ x)
       have r₂ := eq11721
       grind)
    | exact resolve eq28 eq11721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11721
  have eq12188 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12187
  have eq12193 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq12164
  have eq12195 : (M.op x y) = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11750 eq12188
    | exact resolve eq12188 eq11750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11750 eq12188
  have eq12200 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq12193
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq12193 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12193
  have eq12204 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12195 eq12200
    | exact resolve eq12200 eq12195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12195 eq12200
  have eq12205 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq1119 (σ x)
       grind)
    | (have r₁ := eq12204
       have r₂ := eq1119 (σ y)
       grind)
    | (have r₁ := eq12204
       have r₂ := eq1119 (σ x)
       grind)
    | exact resolve eq12204 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119 eq12204
  have eq12227 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12205 eq750
    | (have j0 := eq750 (σ x) (σ x)
       grind)
    | (have r₁ := eq750 (σ x) (σ x)
       have r₂ := eq12205
       grind)
    | (have r₁ := eq750 x (M.op x y)
       have r₂ := eq12205
       grind)
    | exact resolve eq750 eq12205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750 eq12205
  have eq12228 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12227
  have eq12229 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12228
  have eq12276 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12229 eq1078
    | exact resolve eq1078 eq12229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078 eq12229
  have eq12312 : (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12276
  have eq12348 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12312 eq40
    | exact resolve eq40 eq12312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq12312
  have eq12355 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq12348
    | exact resolve eq12348 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12348
  have eq12365 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12355 eq1120
    | (have j0 := eq1120 (σ (M.op x y))
       grind)
    | exact resolve eq1120 eq12355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120 eq12355
  have eq12369 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12365
  have eq12377 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq12369
       have r₂ := eq27
       grind)
    | exact resolve eq12369 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12369
  have eq15575 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq2066
    | (have j0 := eq2066 (σ y) X0
       grind)
    | exact resolve eq2066 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2066
  have eq15649 : ∀ X0 : G, y = (k y (τ (σ y))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15575 eq220
    | (have j1 := eq15575 X0
       grind)
    | exact resolve eq220 eq15575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq15672 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15575 eq28
    | (have j0 := eq28 (σ y) (σ y)
       have j1 := eq15575 X0
       grind)
    | (have r₁ := eq28 (σ y) (σ y)
       have r₂ := eq15575 X0
       grind)
    | (have r₁ := eq28 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq15575 (σ x)
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq15575 X0
       grind)
    | exact resolve eq28 eq15575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq15575
  have eq15673 : ∀ X0 : G, (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq15672 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15672
  have eq15691 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1887 eq15673
    | (have j0 := eq15673 X0
       grind)
    | exact resolve eq15673 eq1887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1887 eq15673
  have eq15694 : ∀ X0 : G, y = (k y y) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq32 eq15649
    | (have j0 := eq15649 X0
       grind)
    | exact resolve eq15649 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq15649
  have eq15697 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) X0) ∨ y = (k y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq15694 X0
       grind)
    | (have r₁ := eq15694 X0
       have r₂ := eq1043
       grind)
    | exact resolve eq15694 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15694
  have eq15703 : ∀ X0 : G, (σ x) = (M.op (σ y) X0) ∨ y = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2854 eq15697
    | exact resolve eq15697 eq2854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15727 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ y = (k y y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq15697 eq869
    | exact resolve eq869 eq15697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15697
  have eq15735 : ∀ X0 : G, (σ x) = (M.op (σ y) X0) ∨ y = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq15703 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15703
  have eq15739 : ∀ X0 : G, (σ x) = (M.op (σ y) X0) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2160 eq15735
    | (have j0 := eq15735 X0
       grind)
    | exact resolve eq15735 eq2160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2160 eq15735
  have eq15753 : ∀ X0 : G, (σ x) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2922 eq15691
    | exact resolve eq15691 eq2922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15691
  have eq15787 : ∀ X0 : G, (σ x) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq15753 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15753
  have eq15791 : ∀ X0 : G, (σ x) = (M.op (σ y) X0) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq15787 X0
       grind)
    | (have r₁ := eq15787 X0
       have r₂ := eq2944
       grind)
    | exact resolve eq15787 eq2944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15787
  have eq15817 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq15739 eq869
    | exact resolve eq869 eq15739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15843 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq15791 eq869
    | exact resolve eq869 eq15791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15791
  have eq16156 : ∀ X0 : G, x = (k x (τ (M.op (σ x) X0))) ∨ y = (k y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15727 eq202
    | exact resolve eq202 eq15727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16166 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ y = (k y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15727 eq26
    | (have j1 := eq15727 (σ y) X0
       grind)
    | exact resolve eq26 eq15727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15727
  have eq16318 : x = (k x (τ (M.op (σ x) (σ y)))) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16166 eq16156
    | (have j0 := eq16156 (σ y)
       grind)
    | exact resolve eq16156 eq16166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16156
  have eq18486 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15817 eq26
    | (have j1 := eq15817 (σ y) X0
       grind)
    | exact resolve eq26 eq15817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15817
  have eq18671 : ∀ X0 : G, (σ y) = (M.op (σ x) X0) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2854 eq18486
    | exact resolve eq18486 eq2854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2854 eq18486
  have eq19793 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq15843 eq26
    | (have j1 := eq15843 (σ y) X0
       grind)
    | exact resolve eq26 eq15843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15843
  have eq20006 : ∀ X0 : G, (σ y) = (M.op (σ x) X0) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2922 eq19793
    | exact resolve eq19793 eq2922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2922 eq19793
  have eq20522 : (M.op (σ x) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1117 eq883
    | exact resolve eq883 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117
  have eq20659 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15739 eq883
    | exact resolve eq883 eq15739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883 eq15739
  have eq20776 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2059 eq20659
    | (have j0 := eq20659 X0
       grind)
    | exact resolve eq20659 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059 eq20659
  have eq20858 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1212 eq20522
    | exact resolve eq20522 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20522
  have eq20901 : ∀ X0 : G, (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) X0) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18671 eq20776
    | (have j0 := eq20776 X0
       grind)
    | exact resolve eq20776 eq18671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18671 eq20776
  have eq20968 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1212 eq20858
    | exact resolve eq20858 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212 eq20858
  have eq20986 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20901 X0
       grind)
    | (have r₁ := eq20901 X0
       have r₂ := eq2866
       grind)
    | exact resolve eq20901 eq2866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2866 eq20901
  have eq21356 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20986 eq16166
    | (have j1 := eq20986 (σ y)
       grind)
    | exact resolve eq16166 eq20986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16166
  have eq21366 : x = (k x (τ (σ x))) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20986 eq202
    | exact resolve eq202 eq20986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq21372 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20986 eq26
    | (have j1 := eq20986 (σ y)
       grind)
    | exact resolve eq26 eq20986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20986
  have eq21405 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq21356
  have eq21472 : x = (k x x) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq21366
    | exact resolve eq21366 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21366
  have eq21474 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq21405
       have r₂ := eq1043
       grind)
    | exact resolve eq21405 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043 eq21405
  have eq21482 : x = (k x x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have j1 := eq1409 x
       grind)
    | (have r₁ := eq21472
       have r₂ := eq1409 y
       grind)
    | (have r₁ := eq21472
       have r₂ := eq1409 x
       grind)
    | exact resolve eq21472 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21472
  have eq21484 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21372 eq21474
    | exact resolve eq21474 eq21372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21372 eq21474
  have eq21491 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq1409 x
       grind)
    | (have r₁ := eq21484
       have r₂ := eq1409 y
       grind)
    | (have r₁ := eq21484
       have r₂ := eq1409 x
       grind)
    | exact resolve eq21484 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21484
  have eq21504 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1496
       have i₂ := eq21482
       grind)
    | exact superpose eq21482 eq1496
    | exact resolve eq1496 eq21482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21536 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq21504
  have eq21561 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq21536
       grind)
    | exact superpose eq21536 eq24
    | exact resolve eq24 eq21536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21536
  have eq21612 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq21561
    | exact resolve eq21561 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21561
  have eq21725 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq21612 eq8345
    | (have j0 := eq8345 X0
       grind)
    | exact resolve eq8345 eq21612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21612
  have eq21765 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1529 eq21725
    | (have j0 := eq21725 X0
       have j1 := eq1529 X0
       grind)
    | exact resolve eq21725 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529 eq21725
  have eq21766 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21765 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21765
  have eq21786 : ∀ X0 : G, (σ x) = (σ y) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1005 eq21766
    | (have j0 := eq21766 X0
       grind)
    | exact resolve eq21766 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21766
  have eq21787 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21786 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21786
  have eq21801 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1496
       have i₂ := eq21491
       grind)
    | exact superpose eq21491 eq1496
    | exact resolve eq1496 eq21491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21491
  have eq21834 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq21801
  have eq21951 : x = (k x (τ (σ x))) ∨ y = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21834 eq16318
    | exact resolve eq16318 eq21834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16318 eq21834
  have eq21965 : x = (k x (τ (σ x))) ∨ y = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq21951
  have eq22001 : x = (k x x) ∨ y = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq21965
    | exact resolve eq21965 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21965
  have eq22018 : x = (k x x) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq1409 x
       grind)
    | (have r₁ := eq22001
       have r₂ := eq1409 y
       grind)
    | (have r₁ := eq22001
       have r₂ := eq1409 x
       grind)
    | exact resolve eq22001 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409 eq22001
  have eq22030 : x = (k x x) ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21482 eq22018
    | exact resolve eq22018 eq21482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21482 eq22018
  have eq22031 : x = (k x x) ∨ y = (M.op x y) := by grind
  clear eq22030
  have eq22048 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1496
       have i₂ := eq22031
       grind)
    | exact superpose eq22031 eq1496
    | exact resolve eq1496 eq22031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496
  have eq22050 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5711
       have i₂ := eq22031
       grind)
    | exact superpose eq22031 eq5711
    | exact resolve eq5711 eq22031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5711
  have eq22063 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq805 x
       have i₂ := eq22031
       grind)
    | exact superpose eq22031 eq805
    | (have j0 := eq805 x
       grind)
    | exact resolve eq805 eq22031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805 eq22031
  have eq22072 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq22063
  have eq22079 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq22050
  have eq22080 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq22048
  have eq22090 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq22072
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22072
    | exact resolve eq22072 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22072
  have eq22100 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq22079
       have r₂ := eq5760
       grind)
    | exact resolve eq22079 eq5760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5760 eq22079
  have eq22335 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22090 eq20006
    | exact resolve eq20006 eq22090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20006 eq22090
  have eq22354 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22335
  have eq22428 : x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq22354
       have r₂ := eq2944
       grind)
    | exact resolve eq22354 eq2944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2944 eq22354
  have eq22459 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22080 eq22428
    | exact resolve eq22428 eq22080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22080 eq22428
  have eq22460 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq22459
  have eq22471 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22460 eq27
    | exact resolve eq27 eq22460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22460
  have eq22734 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22100 eq181
    | exact resolve eq181 eq22100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq22100
  have eq22782 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq22734
    | exact resolve eq22734 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22734
  have eq22787 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5932 eq22782
    | exact resolve eq22782 eq5932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5932 eq22782
  have eq22790 : y = (M.op x y) := by
    first
    | (have r₁ := eq22787
       have r₂ := eq22471
       grind)
    | exact resolve eq22787 eq22471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22471 eq22787
  have eq22792 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq22790
       grind)
    | exact superpose eq22790 eq18
    | exact resolve eq18 eq22790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq22793 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq22790
       grind)
    | exact superpose eq22790 eq24
    | exact resolve eq24 eq22790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq22804 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1874
       have i₂ := eq22790
       grind)
    | exact superpose eq22790 eq1874
    | exact resolve eq1874 eq22790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1874 eq22790
  have eq22825 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq22793 eq20
    | exact resolve eq20 eq22793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22828 : (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq22793 eq15
    | exact resolve eq15 eq22793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22972 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq22825 eq8345
    | (have j0 := eq8345 X0
       grind)
    | exact resolve eq8345 eq22825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8345
  have eq22997 : ∀ X0 : G, (σ x) = (σ y) ∨ x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1005 eq22972
    | (have j0 := eq22972 X0
       grind)
    | exact resolve eq22972 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005 eq22972
  have eq22998 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq22997 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22997
  have eq28460 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq22998 eq869
    | exact resolve eq869 eq22998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869 eq22998
  have eq33079 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq22792
       have i₂ := eq28460 sF0 x
       grind)
    | (have i₁ := eq22792
       have i₂ := eq28460 X0 sF0
       grind)
    | exact superpose eq28460 eq22792
    | (have j1 := eq28460 y X0
       grind)
    | exact resolve eq22792 eq28460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22792 eq28460
  have eq33255 : ∀ X0 : G, (M.op x y) ≠ (M.op (M.op x y) X0) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq882 x x
       have i₂ := eq33079 x
       grind)
    | exact superpose eq33079 eq882
    | exact resolve eq882 eq33079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882
  have eq33259 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ (M.op (M.op x y) X0))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2396 x x
       have i₂ := eq33079 x
       grind)
    | exact superpose eq33079 eq2396
    | exact resolve eq2396 eq33079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2396 eq33079
  have eq33282 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ (M.op (M.op x y) X0))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq33259
    | (have j0 := eq33259 X0
       grind)
    | exact resolve eq33259 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33259
  have eq33286 : ∀ X0 : G, (M.op x y) ≠ (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq22804 eq33255
    | (have j0 := eq33255 X0
       grind)
    | exact resolve eq33255 eq22804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22804 eq33255
  have eq33299 : ∀ X0 : G, (σ y) = (k (σ x) (σ (M.op (M.op x y) X0))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq22825 eq33282
    | (have j0 := eq33282 X0
       grind)
    | exact resolve eq33282 eq22825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33282
  have eq33302 : ∀ X0 : G, (σ y) = (k (σ x) (σ (M.op (M.op x y) X0))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq33299 X0
       grind)
    | (have r₁ := eq33299 X0
       have r₂ := eq33286 X0
       grind)
    | exact resolve eq33299 eq33286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33286 eq33299
  have eq33303 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21787 eq33302
    | exact resolve eq33302 eq21787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21787 eq33302
  have eq33304 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33303
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq33303
    | exact resolve eq33303 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33303
  have eq39148 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33304 eq20968
    | exact resolve eq20968 eq33304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20968
  have eq39183 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq39148
  have eq39227 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39183 eq27
    | exact resolve eq27 eq39183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39183
  have eq39273 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq39227
       have r₂ := eq22825
       grind)
    | exact resolve eq39227 eq22825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22825 eq39227
  have eq39332 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39273 eq9210
    | exact resolve eq9210 eq39273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9210
  have eq39413 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq39332
  have eq39546 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39413 eq33304
    | exact resolve eq33304 eq39413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33304 eq39413
  have eq39572 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq39546
  have eq39585 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39273 eq39572
    | exact resolve eq39572 eq39273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39273 eq39572
  have eq39586 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq39585
  have eq39670 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39586 eq22828
    | exact resolve eq22828 eq39586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22828 eq39586
  have eq39722 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq39670
    | exact resolve eq39670 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq39670
  have eq39723 : x = (M.op x y) := by grind
  clear eq39722
  have eq39754 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq39723
       grind)
    | exact superpose eq39723 eq22
    | exact resolve eq22 eq39723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq39723
  have eq39907 : (σ x) = (σ y) := by
    first
    | exact superpose eq39754 eq22793
    | exact resolve eq22793 eq39754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22793
  have eq39908 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq39754 eq20
    | exact resolve eq20 eq39754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq39754
  have eq40082 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq39907 eq26
    | exact resolve eq26 eq39907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq40321 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39908 eq12377
    | exact resolve eq12377 eq39908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12377
  have eq40357 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq40321
       have r₂ := eq5463
       grind)
    | exact resolve eq40321 eq5463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5463 eq40321
  have eq40380 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40082 eq40357
    | exact resolve eq40357 eq40082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40082 eq40357
  have eq40395 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39907 eq40380
    | exact resolve eq40380 eq39907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39907 eq40380
  have eq40396 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq40395
  have eq40415 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq40396 eq27
    | exact resolve eq27 eq40396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq40396
  have eq40521 : False := by grind
  exact eq40521

/-- `Equation4069`: `x ◇ x = ((x ◇ x) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_pyy_pyx_Equation4069 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4069 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4069.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X2) := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
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
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq124 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq50
    | (have j0 := eq50 x
       grind)
    | exact resolve eq50 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq50
    | (have j0 := eq50 (M.op x y)
       grind)
    | exact resolve eq50 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq145 : ∀ X0 : G, (k (k X0 x) x) = (τ (k (k (σ X0) (σ x)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq59 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq59
    | exact resolve eq59 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq16 (M.op X0 X0) x X2
       have i₂ := eq16 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq37 (M.op sF0 sF0)
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq37
    | exact resolve eq37 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq182 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq181
    | exact resolve eq181 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq192 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq90 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq90
    | exact resolve eq90 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq203 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq29 eq192
    | exact resolve eq192 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq210 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq107 (M.op sF3 sF3)
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq107
    | exact resolve eq107 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq31 eq210
    | exact resolve eq210 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq210
  have eq228 : (τ (σ (M.op x y))) = (k (M.op x y) (τ (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | (have i₁ := eq124 (M.op sF1 sF1)
       have i₂ := eq174 sF1
       grind)
    | exact superpose eq174 eq124
    | exact resolve eq124 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq239 : (M.op x y) = (k (M.op x y) (τ (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | exact superpose eq28 eq228
    | exact resolve eq228 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq315 : ∀ X0 : G, (k (k (σ (M.op x y)) (σ x)) (σ X0)) = (σ (k (k (M.op x y) x) X0)) := by
    intro X0
    first
    | exact superpose eq131 eq34
    | exact resolve eq34 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq330 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq174 (τ X0)
       grind)
    | exact superpose eq174 eq34
    | exact resolve eq34 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k (τ X0) X1) X2
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq10
    | exact resolve eq10 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq330 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq330
    | exact resolve eq330 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq400 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq547 : ∀ X0 X1 : G, (k (k X0 x) (τ X1)) = (τ (k (k (σ X0) (σ x)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq400 (k X0 x) X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq400
    | exact resolve eq400 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq730 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X0 X1
       have i₂ := eq176 X0 X2
       grind)
    | (have i₁ := eq176 X0 X2
       have i₂ := eq176 X0 (M.op X0 X0)
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq736 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq174 (M.op X0 X0)
       have i₂ := eq176 X0 X1
       grind)
    | (have i₁ := eq174 (M.op X0 X0)
       have i₂ := eq176 X0 (M.op X0 X0)
       grind)
    | exact superpose eq176 eq174
    | exact resolve eq174 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq782 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 x (M.op X0 X0)
       have i₂ := eq176 X0 x
       grind)
    | (have i₁ := eq11 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq176 X0 x
       grind)
    | exact superpose eq176 eq11
    | (have j0 := eq11 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact resolve eq11 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq786 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 x
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq176
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq788 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X1) X2) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq792 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X1 X0
       have i₂ := eq11 X0 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq176
    | (have j1 := eq11 (M.op X1 X1) (M.op X1 X1)
       grind)
    | exact resolve eq176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 (M.op (M.op X1 X1) X2)) ∨ (M.op (M.op X1 X1) X2) = (M.op (M.op (M.op X1 X1) X2) (M.op (M.op X1 X1) X2)) ∨ (M.op X0 X0) = (M.op (M.op X1 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq11 X0 (M.op (M.op X1 X1) X2)
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 (M.op (M.op X1 X1) X2) (M.op (M.op X1 X1) X2)
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq795 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 X1
       have i₂ := eq11 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq11 eq176
    | (have j1 := eq11 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq804 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq809 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq813 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq814 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq813 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813
  have eq830 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq795 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq832 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X1) X2) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq788 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq834 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq786 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq836 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq782 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq851 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 (M.op (M.op X1 X1) X2)) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X2) ∨ (M.op X0 X0) = (M.op (M.op X1 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq794 X0 X1 X2
       have i₂ := eq16 X1 X2 (M.op (M.op X1 X1) X2)
       grind)
    | exact superpose eq16 eq794
    | (have j0 := eq794 X0 X1 X2
       grind)
    | exact resolve eq794 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq852 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq792 X0 X1
       have j1 := eq12 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq792 X0 X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq792 (M.op X1 X1) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq792 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq792 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq880 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X1) = (M.op X2 X2) ∨ (M.op X0 X0) = (k X2 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op X0 X0) X1)
       have i₂ := eq16 X0 X1 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq16 eq12
    | (have j0 := eq12 X2 (M.op (M.op X0 X0) X1)
       grind)
    | exact resolve eq12 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq884 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X2 (M.op (M.op X0 X0) X1)) ∨ (M.op (M.op X0 X0) X1) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq880 X0 X1 X2
       have j1 := eq851 X2 X0 X1
       grind)
    | (have r₁ := eq880 X1 X2 X2
       have r₂ := eq851 X0 X1 X2
       grind)
    | (have r₁ := eq880 X1 X2 X2
       have r₂ := eq851 X1 X1 X2
       grind)
    | (have r₁ := eq880 (M.op X1 X1) (M.op (M.op X1 X1) (M.op X1 X1)) X2
       have r₂ := eq851 (M.op (M.op X1 X1) (M.op X1 X1)) X1 (M.op X1 X1)
       grind)
    | exact resolve eq880 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851 eq880
  have eq885 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq814 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq814
    | (have j0 := eq814 (σ X0)
       grind)
    | exact resolve eq814 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq933 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) (M.op (k X0 X0) X1)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq736 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq736
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq736 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq944 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) (M.op (k X0 X0) X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq933 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933
  have eq1786 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq804
       grind)
    | exact superpose eq804 eq39
    | exact resolve eq39 eq804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1787 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1786
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1786
    | exact resolve eq1786 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786
  have eq1789 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1787
    | exact resolve eq1787 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1787
  have eq8301 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (k X2 (M.op (M.op (M.op X0 X0) X1) X3)) ∨ (M.op (M.op (M.op X0 X0) X1) X3) = (M.op X2 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq884 (M.op X0 X0) X1 X2
       have i₂ := eq730 X0 (M.op X0 X0) X2
       grind)
    | (have i₁ := eq884 (M.op X0 X0) X1 X2
       have i₂ := eq730 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq730 eq884
    | exact resolve eq884 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8333 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ x) (σ (M.op (M.op X0 X0) X1))) ∨ (M.op (M.op X0 X0) X1) = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (M.op (M.op X0 X0) X1)
       have i₂ := eq884 X0 X1 x
       grind)
    | exact superpose eq884 eq35
    | (have j1 := eq884 X0 X1 x
       grind)
    | exact resolve eq35 eq884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8334 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ y) (σ (M.op (M.op X0 X0) X1))) ∨ (M.op (M.op X0 X0) X1) = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq36 (M.op (M.op X0 X0) X1)
       have i₂ := eq884 X0 X1 y
       grind)
    | exact superpose eq884 eq36
    | (have j1 := eq884 X0 X1 y
       grind)
    | exact resolve eq36 eq884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8345 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (k X2 (M.op X0 X0)) ∨ (M.op (M.op (M.op X0 X0) X1) X3) = (M.op X2 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8301 X0 X1 X2 X3
       have i₂ := eq16 X0 X1 X3
       grind)
    | exact superpose eq16 eq8301
    | (have j0 := eq8301 X0 X1 X2 X3
       grind)
    | exact resolve eq8301 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8301
  have eq8348 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (k X2 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8345 X0 X1 X2 x
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq8345
    | (have j0 := eq8345 X0 X1 X2 x
       grind)
    | exact resolve eq8345 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8345
  have eq16715 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1789 eq809
    | exact resolve eq809 eq1789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1789
  have eq16722 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq16715
       have r₂ := eq27
       grind)
    | exact resolve eq16715 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16715
  have eq16729 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16722 eq221
    | exact resolve eq221 eq16722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16722
  have eq16747 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq16729
    | exact resolve eq16729 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16729
  have eq16750 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq16747
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq16747
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq16747
       have r₂ := eq13 y x
       grind)
    | exact resolve eq16747 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16747
  have eq16752 : x = (k x (τ (σ x))) ∨ y = (k y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq16750 eq203
    | exact resolve eq203 eq16750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16750
  have eq16767 : x = (k x x) ∨ y = (k y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq16752
    | exact resolve eq16752 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16752
  have eq16769 : y = (k y x) ∨ x = (k x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq16767
       have r₂ := eq13 x x
       grind)
    | exact resolve eq16767 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16767
  have eq16770 : y = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16769
       have i₂ := eq804
       grind)
    | exact superpose eq804 eq16769
    | exact resolve eq16769 eq804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16773 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq804
       have i₂ := eq16769
       grind)
    | exact superpose eq16769 eq804
    | exact resolve eq804 eq16769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq16775 : (σ y) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq16769
       grind)
    | exact superpose eq16769 eq39
    | exact resolve eq39 eq16769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16776 : (σ y) = (k (σ y) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq16775
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16775
    | exact resolve eq16775 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16775
  have eq16778 : x = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq814 x
       grind)
    | (have r₁ := eq16773
       have r₂ := eq814 x
       grind)
    | exact resolve eq16773 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16773
  have eq16781 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq16770
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq16770
       have r₂ := eq13 y x
       grind)
    | exact resolve eq16770 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16770
  have eq16788 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq16776 eq809
    | exact resolve eq809 eq16776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16804 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y X1 x
       have i₂ := eq16778
       grind)
    | exact superpose eq16778 eq16
    | exact resolve eq16 eq16778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16809 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq730 y X1 x
       have i₂ := eq16778
       grind)
    | exact superpose eq16778 eq730
    | exact resolve eq730 eq16778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16778
  have eq16826 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq885 x
       have i₂ := eq16781
       grind)
    | exact superpose eq16781 eq885
    | (have j0 := eq885 x
       grind)
    | exact resolve eq885 eq16781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16781
  have eq16832 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq16826
  have eq16833 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16832
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16832
    | exact resolve eq16832 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16832
  have eq16928 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (σ x) ∨ (σ x) = (k X0 (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq16833 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq16833
       grind)
    | exact resolve eq12 eq16833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16930 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq16833 eq16
    | exact resolve eq16 eq16833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16940 : ∀ X0 : G, (σ x) = (k X0 (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq16928 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16928
  have eq17164 : ∀ X0 : G, (k X0 x) = (M.op x x) ∨ (M.op X0 X0) = x ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq884 x x x
       have i₂ := eq16804 x x
       grind)
    | exact superpose eq16804 eq884
    | exact resolve eq884 eq16804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16804
  have eq17183 : ∀ X0 : G, (k X0 x) = (M.op x x) ∨ (M.op X0 X0) = x ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq17164 X0
       have j1 := eq12 X0 x
       grind)
    | (have r₁ := eq17164 x
       have r₂ := eq12 X0 x
       grind)
    | (have r₁ := eq17164 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq17164 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17164
  have eq17248 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq16809 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq16809 X0 y
       grind)
    | exact superpose eq16809 eq18
    | (have j1 := eq16809 y X0
       grind)
    | exact resolve eq18 eq16809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16809
  have eq17685 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq16833 eq16930
    | exact resolve eq16930 eq16833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16833 eq16930
  have eq17717 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq17685 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17685
  have eq17885 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17717 eq26
    | (have j1 := eq17717 (σ y)
       grind)
    | exact resolve eq26 eq17717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17717
  have eq17911 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y X1 x
       have i₂ := eq17885
       grind)
    | exact superpose eq17885 eq16
    | exact resolve eq16 eq17885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17916 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq730 y X1 x
       have i₂ := eq17885
       grind)
    | exact superpose eq17885 eq730
    | exact resolve eq730 eq17885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17885
  have eq17959 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq17911 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17911
    | (have j0 := eq17911 y X0
       grind)
    | exact resolve eq17911 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18090 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq17916 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq17916 X0 y
       grind)
    | exact superpose eq17916 eq18
    | (have j1 := eq17916 y X0
       grind)
    | exact resolve eq18 eq17916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18118 : ∀ X0 X1 X2 : G, (M.op x X0) = (k X1 (M.op (M.op x X0) X2)) ∨ (M.op X1 X1) = (M.op (M.op x X0) X2) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq884 x X1 X2
       have i₂ := eq17916 x X1
       grind)
    | (have i₁ := eq884 x X1 X2
       have i₂ := eq17916 X0 x
       grind)
    | exact superpose eq17916 eq884
    | exact resolve eq884 eq17916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884
  have eq18144 : ∀ X0 X1 X2 : G, (k X1 x) = (M.op x X0) ∨ (M.op X1 X1) = (M.op (M.op x X0) X2) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq17911 eq18118
    | (have j0 := eq18118 X0 X1 X2
       grind)
    | exact resolve eq18118 eq17911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18118
  have eq18164 : ∀ X0 X1 : G, (k X1 x) = (M.op x X0) ∨ (M.op X1 X1) = x ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq17911 eq18144
    | (have j0 := eq18144 X0 X1 x
       grind)
    | exact resolve eq18144 eq17911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18144
  have eq18168 : ∀ X1 : G, (M.op x y) = (k X1 x) ∨ (M.op X1 X1) = x ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq18090 eq18164
    | (have j0 := eq18164 y X1
       grind)
    | exact resolve eq18164 eq18090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18164
  have eq18527 : ∀ X0 : G, (σ (M.op x x)) = (k X0 (σ x)) ∨ x = (M.op (τ X0) (τ X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq34 X0 x
       have i₂ := eq17183 (τ X0)
       grind)
    | exact superpose eq17183 eq34
    | (have j1 := eq17183 (τ X0)
       grind)
    | exact resolve eq34 eq17183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18563 : ∀ X0 : G, (M.op x y) = (k X0 x) ∨ x = (k X0 x) ∨ y = (M.op x y) ∨ (M.op X0 X0) = x ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq17248 x
       have i₂ := eq17183 X0
       grind)
    | exact superpose eq17183 eq17248
    | (have j1 := eq17183 X0
       grind)
    | exact resolve eq17248 eq17183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17248
  have eq18575 : ∀ X0 X1 X2 : G, (k X0 x) = (M.op (M.op (k X0 x) X1) X2) ∨ (M.op X0 X0) = x ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 x X1 X2
       have i₂ := eq17183 X0
       grind)
    | exact superpose eq17183 eq16
    | (have j1 := eq17183 X0
       grind)
    | exact resolve eq16 eq17183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17183
  have eq18597 : ∀ X0 : G, (M.op x y) = (k X0 x) ∨ x = (k X0 x) ∨ y = (M.op x y) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have j0 := eq18563 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18563
  have eq18635 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op x x)) ∨ x = (M.op (τ X0) (τ X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18527 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18527
    | (have j0 := eq18527 X0
       grind)
    | exact resolve eq18527 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18527
  have eq20302 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (k (M.op x X0) (M.op x X0)) ∨ (M.op x X0) = (M.op (M.op x X0) X1) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq836 x X1
       have i₂ := eq17916 x X1
       grind)
    | (have i₁ := eq836 x X1
       have i₂ := eq17916 X0 x
       grind)
    | exact superpose eq17916 eq836
    | exact resolve eq836 eq17916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17916
  have eq20303 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x y) X0) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq836 x x
       have i₂ := eq18090 x
       grind)
    | exact superpose eq18090 eq836
    | exact resolve eq836 eq18090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20377 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq836 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20414 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq17959 eq20303
    | (have j0 := eq20303 X0
       grind)
    | exact resolve eq20303 eq17959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17959 eq20303
  have eq20415 : ∀ X0 X1 : G, x = (k (M.op x X0) (M.op x X0)) ∨ (M.op x X0) = (M.op (M.op x X0) X1) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq17911 eq20302
    | (have j0 := eq20302 X0 X1
       grind)
    | exact resolve eq20302 eq17911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20302
  have eq20461 : ∀ X0 : G, x = (k (M.op x X0) (M.op x X0)) ∨ x = (M.op x X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq17911 eq20415
    | (have j0 := eq20415 X0 x
       grind)
    | exact resolve eq20415 eq17911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17911 eq20415
  have eq20480 : ∀ X0 : G, x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18090 eq20461
    | (have j0 := eq20461 y
       grind)
    | exact resolve eq20461 eq18090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20461
  have eq20490 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18090 eq20480
    | (have j0 := eq20480 y
       grind)
    | exact resolve eq20480 eq18090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18090 eq20480
  have eq22407 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ x)) ∨ x = (M.op (τ X0) (τ X0)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 x
       have i₂ := eq18168 (τ X0)
       grind)
    | exact superpose eq18168 eq34
    | (have j1 := eq18168 (τ X0)
       grind)
    | exact resolve eq34 eq18168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq18168
  have eq22505 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ x)) ∨ x = (M.op (τ X0) (τ X0)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq22407 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22407
    | (have j0 := eq22407 X0
       grind)
    | exact resolve eq22407 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22407
  have eq22535 : ∀ X0 : G, x = (M.op (τ X0) (τ X0)) ∨ (σ (M.op x y)) = (k X0 (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq22505
    | (have j0 := eq22505 X0
       grind)
    | exact resolve eq22505 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22505
  have eq23194 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20414 eq174
    | exact resolve eq174 eq20414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20414
  have eq23652 : x ≠ (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23194
  have eq23660 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq23652
       have r₂ := eq20490
       grind)
    | exact resolve eq23652 eq20490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20490 eq23652
  have eq23676 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23660 eq41
    | exact resolve eq41 eq23660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23691 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq23676
    | exact resolve eq23676 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23676
  have eq23698 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23691
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23691
    | exact resolve eq23691 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23691
  have eq23712 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23698 eq834
    | (have j0 := eq834 (σ (M.op x y)) x
       grind)
    | exact resolve eq834 eq23698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq28938 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16788
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq16788
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq16788 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28951 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq16788 eq830
    | exact resolve eq830 eq16788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28954 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq16788 eq852
    | exact resolve eq852 eq16788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq28961 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq16788 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq16788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28962 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by grind
  clear eq28961
  have eq28964 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    intro X0
    first
    | (have j0 := eq28951 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28951
  have eq28966 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq28938
  have eq28967 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    intro X0
    first
    | (have j0 := eq28954 X0
       have j1 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq28954 (σ x)
       have r₂ := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq28954 X0
       have r₂ := eq12 X0 (σ x)
       grind)
    | exact resolve eq28954 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28954
  have eq28975 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq28962 eq28966
    | exact resolve eq28966 eq28962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28962 eq28966
  have eq28976 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by grind
  clear eq28975
  have eq29191 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16940 eq107
    | (have j1 := eq16940 (σ y)
       grind)
    | exact resolve eq107 eq16940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq16940
  have eq29242 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq29191
    | exact resolve eq29191 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29191
  have eq29357 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq28976 eq115
    | exact resolve eq115 eq28976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq28976
  have eq29387 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq29357
    | exact resolve eq29357 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29357
  have eq30212 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq18597 x
       grind)
    | exact superpose eq18597 eq35
    | (have j1 := eq18597 x
       grind)
    | exact resolve eq35 eq18597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq30270 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq30212
       have r₂ := eq13 x x
       grind)
    | exact resolve eq30212 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30212
  have eq30322 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq30270
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30270
    | exact resolve eq30270 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30270
  have eq30361 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq30322
    | exact resolve eq30322 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30322
  have eq30424 : (τ (σ (M.op x y))) = (k x x) ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30361 eq97
    | exact resolve eq97 eq30361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30361
  have eq30465 : (M.op x y) = (k x x) ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq30424
    | exact resolve eq30424 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30424
  have eq30504 : x ≠ (M.op x y) ∨ x = (k x x) ∨ y = (M.op x y) := by grind
  clear eq30465
  have eq33156 : y = (k y (τ (σ x))) ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29242 eq221
    | exact resolve eq221 eq29242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq29242
  have eq33188 : y = (k y x) ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq33156
    | exact resolve eq33156 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33156
  have eq33194 : y = (k y x) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq33188
       have r₂ := eq13 y x
       grind)
    | exact resolve eq33188 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33188
  have eq33211 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18597 y
       have i₂ := eq33194
       grind)
    | exact superpose eq33194 eq18597
    | (have j0 := eq18597 y
       grind)
    | exact resolve eq18597 eq33194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18597
  have eq33215 : x ≠ y ∨ x = (k y x) ∨ y = (M.op x y) := by grind
  clear eq33194
  have eq33218 : y = (M.op x y) ∨ x = y ∨ x = (M.op y y) ∨ x = (k y x) := by grind
  clear eq33211
  have eq33229 : x = (k y x) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq33218
       have r₂ := eq33215
       grind)
    | exact resolve eq33218 eq33215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33215 eq33218
  have eq33259 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq33229
       grind)
    | exact superpose eq33229 eq36
    | exact resolve eq36 eq33229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq33285 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq33259
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq33259
    | exact resolve eq33259 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33259
  have eq33418 : x = (k x (τ (σ x))) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq29387 eq203
    | exact resolve eq203 eq29387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29387
  have eq33465 : x = (k x x) ∨ x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq33418
    | exact resolve eq33418 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33418
  have eq33466 : x = (k y y) ∨ x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq33465
  have eq33476 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ y = (M.op y y) ∨ x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq832 y X1 x
       have i₂ := eq33466
       grind)
    | exact superpose eq33466 eq832
    | (have j0 := eq832 y X1 x
       grind)
    | exact resolve eq832 eq33466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq41723 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ (M.op x y)) = (k X0 (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq358 X0
       have i₂ := eq22535 X0
       grind)
    | exact superpose eq22535 eq358
    | (have j1 := eq22535 X0
       grind)
    | exact resolve eq358 eq22535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22535
  have eq41773 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ x)) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41723 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq41723
    | (have j0 := eq41723 X0
       grind)
    | exact resolve eq41723 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41723
  have eq41836 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41773 eq814
    | (have j0 := eq814 (σ x)
       have j1 := eq41773 (σ x)
       grind)
    | (have r₁ := eq814 (σ x)
       have r₂ := eq41773 (σ x)
       grind)
    | exact resolve eq814 eq41773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41843 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq41773 eq944
    | (have j0 := eq944 (σ x) x
       have j1 := eq41773 (σ x)
       grind)
    | exact resolve eq944 eq41773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq41924 : (τ (σ (M.op x y))) = (k x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41773 eq97
    | (have j1 := eq41773 (σ x)
       grind)
    | exact resolve eq97 eq41773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq41773
  have eq42002 : (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq41924
    | exact resolve eq41924 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41924
  have eq42052 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq41843 X0
       have j1 := eq814 (σ x)
       grind)
    | (have r₁ := eq41843 X0
       have r₂ := eq814 (σ x)
       grind)
    | exact resolve eq41843 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41843
  have eq42057 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq814 (σ x)
       grind)
    | (have r₁ := eq41836
       have r₂ := eq814 (σ x)
       grind)
    | exact resolve eq41836 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41836
  have eq42137 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq42002 eq814
    | (have j0 := eq814 (σ x)
       grind)
    | (have r₁ := eq814 (σ x)
       have r₂ := eq42002
       grind)
    | exact resolve eq814 eq42002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42155 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq42137
  have eq42232 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq42155 eq836
    | exact resolve eq836 eq42155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42155
  have eq42265 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq42002 eq42232
    | (have j0 := eq42232 X0
       grind)
    | exact resolve eq42232 eq42002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42002 eq42232
  have eq42266 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq42265 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42265
  have eq42284 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq42266 eq26
    | (have j1 := eq42266 (σ y)
       grind)
    | exact resolve eq26 eq42266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42266
  have eq42350 : (M.op x y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq42284
  have eq42379 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq42350
       grind)
    | exact superpose eq42350 eq39
    | exact resolve eq39 eq42350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42350
  have eq42426 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq42379
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq42379
    | exact resolve eq42379 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42379
  have eq42434 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq42426
    | exact resolve eq42426 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42426
  have eq55139 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23712 eq26
    | (have j1 := eq23712 (σ y)
       grind)
    | exact resolve eq26 eq23712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23712
  have eq55419 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55139 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq55139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55139
  have eq55420 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq55419
  have eq55491 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42434 eq55420
    | exact resolve eq55420 eq42434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55420
  have eq55515 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq55491
       have r₂ := eq27
       grind)
    | exact resolve eq55491 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55491
  have eq55538 : (M.op x y) = (k (M.op x y) (τ (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55515 eq239
    | exact resolve eq239 eq55515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq55543 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55515 eq42052
    | exact resolve eq42052 eq55515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42052
  have eq55554 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55515 eq174
    | exact resolve eq174 eq55515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55515
  have eq55582 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq55543
  have eq55597 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23698 eq55554
    | exact resolve eq55554 eq23698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55554
  have eq55599 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23698 eq55582
    | exact resolve eq55582 eq23698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23698 eq55582
  have eq55600 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq55538
    | exact resolve eq55538 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55538
  have eq55603 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq55599
       have r₂ := eq42057
       grind)
    | exact resolve eq55599 eq42057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42057 eq55599
  have eq55635 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55600 eq23660
    | exact resolve eq23660 eq55600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23660 eq55600
  have eq55668 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq55635
  have eq55713 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq55668 eq27
    | exact resolve eq27 eq55668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55668
  have eq55786 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq55603 eq836
    | exact resolve eq836 eq55603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55603
  have eq55830 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq42434 eq55786
    | (have j0 := eq55786 X0
       grind)
    | exact resolve eq55786 eq42434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42434 eq55786
  have eq55834 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq55597 eq55830
    | (have j0 := eq55830 X0
       grind)
    | exact resolve eq55830 eq55597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55597 eq55830
  have eq55835 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq55834 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55834
  have eq56026 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55835 eq26
    | (have j1 := eq55835 (σ y)
       grind)
    | exact resolve eq26 eq55835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55835
  have eq56109 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq56026
  have eq56125 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq56109 eq27
    | exact resolve eq27 eq56109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71611 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq18575 y X1 x
       have i₂ := eq33229
       grind)
    | exact superpose eq33229 eq18575
    | (have j0 := eq18575 y X1 x
       grind)
    | exact resolve eq18575 eq33229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18575 eq33229
  have eq71695 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq71611 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71611
  have eq71764 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq71695 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq71695
    | (have j0 := eq71695 y X0
       grind)
    | exact resolve eq71695 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71816 : ∀ X1 X2 : G, (M.op x X1) = (M.op x X2) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X1 X2
    first
    | (have i₁ := eq730 (M.op x x) X1 X2
       have i₂ := eq71695 x (M.op x x)
       grind)
    | exact superpose eq71695 eq730
    | exact resolve eq730 eq71695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71695
  have eq72866 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq71816 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq71816 X0 y
       grind)
    | exact superpose eq71816 eq18
    | (have j1 := eq71816 y X0
       grind)
    | exact resolve eq18 eq71816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71816
  have eq73186 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ (M.op (M.op x y) X0))) ∨ (M.op y y) = (M.op (M.op x y) X0) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8334 x x
       have i₂ := eq72866 x
       grind)
    | exact superpose eq72866 eq8334
    | exact resolve eq8334 eq72866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8334 eq72866
  have eq73226 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ (M.op (M.op x y) X0))) ∨ (M.op y y) = (M.op (M.op x y) X0) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq73186
    | (have j0 := eq73186 X0
       grind)
    | exact resolve eq73186 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73186
  have eq73248 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op (M.op x y) X0) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq71764 eq73226
    | (have j0 := eq73226 X0
       grind)
    | exact resolve eq73226 eq71764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73226
  have eq73259 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op (M.op x y) X0) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq73248 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq73248
    | (have j0 := eq73248 X0
       grind)
    | exact resolve eq73248 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73248
  have eq73266 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ (M.op y y) = (M.op (M.op x y) X0) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq33285 eq73259
    | (have j0 := eq73259 X0
       grind)
    | exact resolve eq73259 eq33285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33285 eq73259
  have eq73269 : ∀ X0 : G, (M.op y y) = (M.op (M.op x y) X0) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq73266 X0
       grind)
    | (have r₁ := eq73266 X0
       have r₂ := eq56125
       grind)
    | exact resolve eq73266 eq56125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73266
  have eq73271 : x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq71764 eq73269
    | exact resolve eq73269 eq71764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71764 eq73269
  have eq73272 : x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq73271
  have eq73277 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y X1 x
       have i₂ := eq73272
       grind)
    | exact superpose eq73272 eq16
    | exact resolve eq16 eq73272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73282 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq730 y X1 x
       have i₂ := eq73272
       grind)
    | exact superpose eq73272 eq730
    | exact resolve eq730 eq73272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73287 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq836 y x
       have i₂ := eq73272
       grind)
    | exact superpose eq73272 eq836
    | exact resolve eq836 eq73272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73272
  have eq73453 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq73277 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq73277
    | (have j0 := eq73277 y X0
       grind)
    | exact resolve eq73277 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73277
  have eq73569 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq73453 eq182
    | exact resolve eq182 eq73453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73583 : (M.op x y) = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq73453 eq174
    | exact resolve eq174 eq73453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73621 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq73569
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq73569
    | exact resolve eq73569 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73569
  have eq73838 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq73282 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq73282 X0 y
       grind)
    | exact superpose eq73282 eq18
    | (have j1 := eq73282 y X0
       grind)
    | exact resolve eq18 eq73282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73282
  have eq74084 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ x)) ∨ x = (M.op (τ X0) (τ X0)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18635 X0
       have i₂ := eq73838 x
       grind)
    | exact superpose eq73838 eq18635
    | (have j0 := eq18635 X0
       grind)
    | exact resolve eq18635 eq73838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18635
  have eq74136 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x y) X0) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq836 x x
       have i₂ := eq73838 x
       grind)
    | exact superpose eq73838 eq836
    | exact resolve eq836 eq73838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq74142 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ (M.op (M.op x y) X0))) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8333 x x
       have i₂ := eq73838 x
       grind)
    | exact superpose eq73838 eq8333
    | exact resolve eq8333 eq73838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8333
  have eq74145 : ∀ X0 X1 : G, (k X1 (M.op x y)) = (M.op (M.op x y) X0) ∨ (M.op X1 X1) = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq8348 x X1 x
       have i₂ := eq73838 x
       grind)
    | exact superpose eq73838 eq8348
    | exact resolve eq8348 eq73838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8348
  have eq74171 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ x)) ∨ x = (M.op (τ X0) (τ X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq74084 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74084
  have eq74186 : ∀ X1 : G, x = (k X1 (M.op x y)) ∨ (M.op X1 X1) = (M.op x y) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq73453 eq74145
    | (have j0 := eq74145 x X1
       grind)
    | exact resolve eq74145 eq73453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74145
  have eq74189 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ (M.op (M.op x y) X0))) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq74142
    | (have j0 := eq74142 X0
       grind)
    | exact resolve eq74142 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74142
  have eq74195 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq73453 eq74136
    | (have j0 := eq74136 X0
       grind)
    | exact resolve eq74136 eq73453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74136
  have eq74208 : ∀ X0 : G, x = (M.op (τ X0) (τ X0)) ∨ (σ (M.op x y)) = (k X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq74171
    | (have j0 := eq74171 X0
       grind)
    | exact resolve eq74171 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74171
  have eq74213 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq73453 eq74189
    | (have j0 := eq74189 X0
       grind)
    | exact resolve eq74189 eq73453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74189
  have eq74219 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq74213 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq74213
    | (have j0 := eq74213 X0
       grind)
    | exact resolve eq74213 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74213
  have eq75434 : (σ x) = (k (k (σ (M.op x y)) (σ x)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (k (M.op x y) x) (k (M.op x y) x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq74186 eq315
    | (have j1 := eq74186 (k (M.op x y) x)
       grind)
    | exact resolve eq315 eq74186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315 eq74186
  have eq75514 : (σ x) = (k (k (σ (M.op x y)) (σ x)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (k (M.op x y) x) (k (M.op x y) x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq75434
    | exact resolve eq75434 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75434
  have eq75546 : (σ x) = (k (k (σ (M.op x y)) (σ x)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (k (M.op x y) x) (k (M.op x y) x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq75514
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq75514
    | exact resolve eq75514 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75514
  have eq75560 : (σ x) = (k (k (σ (M.op x y)) (σ x)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq73583 eq75546
    | exact resolve eq75546 eq73583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73583 eq75546
  have eq75565 : (σ x) = (k (k (σ (M.op x y)) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq73453 eq75560
    | exact resolve eq75560 eq73453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73453 eq75560
  have eq75568 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq73621 eq75565
    | exact resolve eq75565 eq73621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73621 eq75565
  have eq75576 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq75568 eq133
    | exact resolve eq133 eq75568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq75568
  have eq75617 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq75576
    | exact resolve eq75576 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75576
  have eq75768 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq74195 eq174
    | exact resolve eq174 eq74195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74195
  have eq76046 : x ≠ (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq75768
  have eq76060 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq76046
       have r₂ := eq75617
       grind)
    | exact resolve eq76046 eq75617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75617 eq76046
  have eq76089 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq76060 eq41
    | exact resolve eq41 eq76060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq76060
  have eq76122 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq76089
    | exact resolve eq76089 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76089
  have eq76129 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq76122
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq76122
    | exact resolve eq76122 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76122
  have eq78049 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq73287 y
       have i₂ := eq73838 x
       grind)
    | (have i₁ := eq73287 x
       have i₂ := eq73838 x
       grind)
    | exact superpose eq73838 eq73287
    | (have j0 := eq73287 y
       grind)
    | exact resolve eq73287 eq73838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73287 eq73838
  have eq78183 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq78049
  have eq78271 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq78183
       grind)
    | exact superpose eq78183 eq39
    | exact resolve eq39 eq78183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78335 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq78271
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq78271
    | exact resolve eq78271 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78271
  have eq78353 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq78335
    | exact resolve eq78335 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78335
  have eq79724 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ (M.op x y)) = (k X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq358 X0
       have i₂ := eq74208 X0
       grind)
    | exact superpose eq74208 eq358
    | (have j1 := eq74208 X0
       grind)
    | exact resolve eq358 eq74208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq79738 : ∀ X0 : G, (τ X0) = (k (τ X0) x) ∨ (σ (M.op x y)) = (k X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq174 (τ X0)
       have i₂ := eq74208 X0
       grind)
    | exact superpose eq74208 eq174
    | (have j1 := eq74208 X0
       grind)
    | exact resolve eq174 eq74208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74208
  have eq79782 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ x)) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq79724 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq79724
    | (have j0 := eq79724 X0
       grind)
    | exact resolve eq79724 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79724
  have eq79879 : ∀ X0 : G, (τ (σ (M.op x y))) = (k X0 x) ∨ (σ X0) = (k (σ X0) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq79782 eq59
    | (have j1 := eq79782 (σ X0)
       grind)
    | exact resolve eq59 eq79782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79782
  have eq80120 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ x)) ∨ (M.op x y) = (k X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28 eq79879
    | (have j0 := eq79879 X0
       grind)
    | exact resolve eq79879 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79879
  have eq82891 : ∀ X0 : G, (σ (M.op x y)) = (k (σ X0) (σ x)) ∨ (k X0 x) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq79738 (σ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq79738
    | (have j0 := eq79738 (σ X0)
       grind)
    | exact resolve eq79738 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79738
  have eq83174 : ∀ X0 : G, (τ (σ (M.op x y))) = (k X0 x) ∨ (k X0 x) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq82891 eq59
    | (have j1 := eq82891 X0
       grind)
    | exact resolve eq59 eq82891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82891
  have eq83251 : ∀ X0 : G, (M.op x y) = (k X0 x) ∨ (k X0 x) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28 eq83174
    | (have j0 := eq83174 X0
       grind)
    | exact resolve eq83174 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq83174
  have eq83434 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (k X0 x) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq83251 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83251
  have eq84155 : ∀ X0 : G, (τ (k (σ X0) (σ x))) = (k (k X0 x) x) ∨ (M.op x y) = (k X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq80120 eq145
    | (have j1 := eq80120 X0
       grind)
    | exact resolve eq145 eq80120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq80120
  have eq84237 : ∀ X0 : G, (k X0 x) = (k (k X0 x) x) ∨ (M.op x y) = (k X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq59 eq84155
    | (have j0 := eq84155 X0
       grind)
    | exact resolve eq84155 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq84155
  have eq84263 : ∀ X0 : G, (k X0 x) = (k (k X0 x) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq84237 X0
       have j1 := eq83434 (k X0 x)
       grind)
    | (have r₁ := eq84237 X0
       have r₂ := eq83434 (k X0 x)
       grind)
    | (have r₁ := eq84237 X0
       have r₂ := eq83434 y
       grind)
    | exact resolve eq84237 eq83434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83434 eq84237
  have eq84373 : ∀ X0 : G, (σ (k (τ X0) x)) = (k (k X0 (σ x)) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq337 X0 x x
       have i₂ := eq84263 (τ X0)
       grind)
    | exact superpose eq84263 eq337
    | exact resolve eq337 eq84263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337 eq84263
  have eq84479 : ∀ X0 : G, (σ (k (τ X0) x)) = (k (k X0 (σ x)) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq84373 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq84373
    | (have j0 := eq84373 X0
       grind)
    | exact resolve eq84373 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84373
  have eq84497 : ∀ X0 : G, (k (σ (τ X0)) (σ x)) = (k (k X0 (σ x)) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq84479 X0
       have i₂ := eq39 (τ X0)
       grind)
    | exact superpose eq39 eq84479
    | exact resolve eq84479 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84479
  have eq84507 : ∀ X0 : G, (k X0 (σ x)) = (k (k X0 (σ x)) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq84497 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq84497
    | exact resolve eq84497 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84497
  have eq84594 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq809 eq84507
    | exact resolve eq84507 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809 eq84507
  have eq84733 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq56109 eq84594
    | exact resolve eq84594 eq56109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84594
  have eq84747 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq84733
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq84733
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq84733 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84733
  have eq84797 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq84747 eq78353
    | exact resolve eq78353 eq84747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78353 eq84747
  have eq84827 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq84797
  have eq84851 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq84827
       have r₂ := eq55713
       grind)
    | exact resolve eq84827 eq55713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55713 eq84827
  have eq84885 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq84851 eq16
    | exact resolve eq16 eq84851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84851
  have eq85423 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq84885
    | (have j0 := eq84885 (σ y) X0
       grind)
    | exact resolve eq84885 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84885
  have eq85583 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq56109 eq85423
    | exact resolve eq85423 eq56109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56109 eq85423
  have eq85624 : x = (k x (τ (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq85583 eq203
    | exact resolve eq203 eq85583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85583
  have eq85784 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq85624
    | exact resolve eq85624 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85624
  have eq85785 : x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq85784
       have r₂ := eq30504
       grind)
    | exact resolve eq85784 eq30504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30504 eq85784
  have eq85825 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq78183
       have i₂ := eq85785
       grind)
    | exact superpose eq85785 eq78183
    | exact resolve eq78183 eq85785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78183
  have eq85827 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq85785
       grind)
    | exact superpose eq85785 eq39
    | exact resolve eq39 eq85785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85785
  have eq85873 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq85825
  have eq85912 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq85827
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq85827
    | exact resolve eq85827 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85827
  have eq85929 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq85873
       grind)
    | exact superpose eq85873 eq18
    | exact resolve eq18 eq85873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85873
  have eq86475 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq85912 eq74219
    | (have j0 := eq74219 X0
       grind)
    | exact resolve eq74219 eq85912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74219 eq85912
  have eq86509 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq86475 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86475
  have eq86530 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq86509 X0
       grind)
    | (have r₁ := eq86509 X0
       have r₂ := eq56125
       grind)
    | exact resolve eq86509 eq56125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86509
  have eq86836 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq86530 eq182
    | exact resolve eq182 eq86530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq86530
  have eq86899 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq86836
    | exact resolve eq86836 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86836
  have eq86906 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq76129 eq86899
    | exact resolve eq86899 eq76129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76129 eq86899
  have eq86909 : y = (M.op x y) := by
    first
    | (have r₁ := eq86906
       have r₂ := eq56125
       grind)
    | exact resolve eq86906 eq56125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56125 eq86906
  have eq86912 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq86909
       grind)
    | exact superpose eq86909 eq18
    | exact resolve eq18 eq86909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq86913 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq86909
       grind)
    | exact superpose eq86909 eq24
    | exact resolve eq24 eq86909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq86939 : (M.op x y) = (k (M.op x y) x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq16769
       have i₂ := eq86909
       grind)
    | exact superpose eq86909 eq16769
    | exact resolve eq16769 eq86909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16769
  have eq86955 : x = (k (M.op x y) (M.op x y)) ∨ x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33466
       have i₂ := eq86909
       grind)
    | exact superpose eq86909 eq33466
    | exact resolve eq33466 eq86909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33466
  have eq86970 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq86913 eq20
    | exact resolve eq20 eq86913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87049 : ∀ X0 : G, (k (k (M.op x y) x) (τ X0)) = (τ (k (k (σ y) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq86913 eq547
    | exact resolve eq547 eq86913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq375155 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq28964 eq26
    | (have j1 := eq28964 (σ y)
       grind)
    | exact resolve eq26 eq28964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28964
  have eq378228 : (τ (M.op (σ x) (σ x))) = (k (k (M.op x y) x) (τ (σ x))) ∨ (σ x) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq28967 eq87049
    | (have j1 := eq28967 (k (σ y) (σ x))
       grind)
    | exact resolve eq87049 eq28967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28967 eq87049
  have eq378553 : (τ (M.op (σ x) (σ x))) = (k (k (M.op x y) x) x) ∨ (σ x) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq378228
    | exact resolve eq378228 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378228
  have eq378653 : (τ (M.op (σ x) (σ x))) = (k (k (M.op x y) x) x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq16776 eq378553
    | exact resolve eq378553 eq16776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16776 eq378553
  have eq378698 : (τ (σ x)) = (k (k (M.op x y) x) x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq16788 eq378653
    | exact resolve eq378653 eq16788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16788 eq378653
  have eq378734 : x = (k (k (M.op x y) x) x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq378698
    | exact resolve eq378698 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378698
  have eq378760 : x = (k (M.op x y) x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq86939 eq378734
    | exact resolve eq378734 eq86939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378734
  have eq378782 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq86939 eq378760
    | exact resolve eq378760 eq86939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378760
  have eq378812 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    intro X0 X1
    first
    | exact superpose eq378782 eq730
    | exact resolve eq730 eq378782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378782
  have eq379533 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq378812 eq26
    | (have j1 := eq378812 (σ y) X0
       grind)
    | exact resolve eq26 eq378812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379534 : ∀ X0 : G, x = (k x (τ (M.op (σ x) X0))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq378812 eq203
    | exact resolve eq203 eq378812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq378812
  have eq406396 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ y = (M.op y y) ∨ x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq86912 eq33476
    | (have j0 := eq33476 y X0
       grind)
    | exact resolve eq33476 eq86912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33476 eq86912
  have eq406488 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) X0) ∨ x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq406396 X0
       have i₂ := eq86909
       grind)
    | exact superpose eq86909 eq406396
    | (have j0 := eq406396 X0
       grind)
    | exact resolve eq406396 eq86909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86909 eq406396
  have eq406601 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) X0) ∨ x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq406488 eq174
    | (have j1 := eq406488 X0
       grind)
    | exact resolve eq174 eq406488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq406488
  have eq406639 : ∀ X0 : G, x = (k x x) ∨ x = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq86955 eq406601
    | (have j0 := eq406601 X0
       grind)
    | exact resolve eq406601 eq86955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86955 eq406601
  have eq406723 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ x = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq39 x
       have i₂ := eq406639 X0
       grind)
    | exact superpose eq406639 eq39
    | (have j1 := eq406639 X0
       grind)
    | exact resolve eq39 eq406639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406755 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ x = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq814 x
       have i₂ := eq406639 X0
       grind)
    | exact superpose eq406639 eq814
    | (have j0 := eq814 x
       have j1 := eq406639 X0
       grind)
    | (have r₁ := eq814 x
       have r₂ := eq406639 X0
       grind)
    | exact resolve eq814 eq406639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406761 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq885 x
       have i₂ := eq406639 X0
       grind)
    | exact superpose eq406639 eq885
    | (have j0 := eq885 x
       have j1 := eq406639 X0
       grind)
    | exact resolve eq885 eq406639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406639
  have eq406786 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq406761 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406761
  have eq406787 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq406755 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406755
  have eq406847 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq406786 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq406786
    | (have j0 := eq406786 X0
       grind)
    | exact resolve eq406786 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406786
  have eq406857 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ x = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq406723 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq406723
    | (have j0 := eq406723 X0
       grind)
    | exact resolve eq406723 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406723
  have eq407121 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq406787 eq830
    | exact resolve eq830 eq406787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830 eq406787
  have eq407146 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq407121 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407121
  have eq407469 : ∀ X0 X1 : G, (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) X0) ∨ x = (M.op (M.op x y) X1) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq406847 eq20377
    | (have j1 := eq406847 X1
       grind)
    | exact resolve eq20377 eq406847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406847
  have eq407516 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op (M.op x y) X1) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq407469 X0 X1
       have j1 := eq406857 X1
       grind)
    | (have r₁ := eq407469 X0 X1
       have r₂ := eq406857 X0
       grind)
    | exact resolve eq407469 eq406857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406857 eq407469
  have eq409750 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq407516 eq26
    | (have j1 := eq407516 (σ y) X0
       grind)
    | exact resolve eq26 eq407516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407516
  have eq410066 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq409750 eq730
    | exact resolve eq730 eq409750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq410090 : ∀ X0 : G, x ≠ (k x x) ∨ x = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq409750 eq20377
    | exact resolve eq20377 eq409750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20377 eq409750
  have eq411620 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq85929
       have i₂ := eq410066 sF0 x
       grind)
    | (have i₁ := eq85929
       have i₂ := eq410066 X0 sF0
       grind)
    | exact superpose eq410066 eq85929
    | (have j1 := eq410066 y X0
       grind)
    | exact resolve eq85929 eq410066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410066
  have eq411655 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq411620 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411620
  have eq413703 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq85929
       have i₂ := eq407146 sF0
       grind)
    | exact superpose eq407146 eq85929
    | (have j1 := eq407146 y
       grind)
    | exact resolve eq85929 eq407146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407146
  have eq413740 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq413703
  have eq416471 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq413740
       grind)
    | exact superpose eq413740 eq39
    | exact resolve eq39 eq413740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq413740
  have eq416606 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq416471
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq416471
    | exact resolve eq416471 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416471
  have eq416632 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq416606
    | exact resolve eq416606 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416606
  have eq416645 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq86970 eq416632
    | exact resolve eq416632 eq86970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416632
  have eq417120 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq416645 eq375155
    | exact resolve eq375155 eq416645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375155 eq416645
  have eq417178 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq417120
  have eq417223 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq814 (σ x)
       grind)
    | (have r₁ := eq417178
       have r₂ := eq814 x
       grind)
    | exact resolve eq417178 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417178
  have eq417577 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq417223 eq379533
    | exact resolve eq379533 eq417223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379533
  have eq417578 : x = (k x (τ (σ x))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq417223 eq379534
    | exact resolve eq379534 eq417223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379534 eq417223
  have eq417615 : x = (k x (τ (σ x))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ x = (M.op x x) := by grind
  clear eq417578
  have eq417616 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ x = (M.op x x) := by grind
  clear eq417577
  have eq417701 : x = (k x (τ (σ x))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | (have j1 := eq13 x (τ (σ x))
       grind)
    | (have r₁ := eq417615
       have r₂ := eq13 x x
       grind)
    | exact resolve eq417615 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417615
  have eq417702 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq410090 y
       grind)
    | (have r₁ := eq417616
       have r₂ := eq410090 x
       grind)
    | exact resolve eq417616 eq410090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410090 eq417616
  have eq417777 : x = (k x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq417701
    | exact resolve eq417701 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq417701
  have eq417778 : x = (k x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq417777
  have eq417779 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq411655 eq417702
    | exact resolve eq417702 eq411655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411655 eq417702
  have eq417780 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq417779
  have eq417789 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq417780 eq27
    | exact resolve eq27 eq417780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417780
  have eq417819 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq417789
       have r₂ := eq86970
       grind)
    | exact resolve eq417789 eq86970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417789
  have eq417821 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq417819 eq27
    | exact resolve eq27 eq417819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417864 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq86970 eq417821
    | exact resolve eq417821 eq86970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417821
  have eq417963 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq814 x
       have i₂ := eq417778
       grind)
    | exact superpose eq417778 eq814
    | (have j0 := eq814 x
       grind)
    | (have r₁ := eq814 x
       have r₂ := eq417778
       grind)
    | exact resolve eq814 eq417778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq417778
  have eq417995 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq417963
  have eq418065 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq417819 eq417995
    | exact resolve eq417995 eq417819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417819 eq417995
  have eq418116 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq418065
       have r₂ := eq417864
       grind)
    | exact resolve eq418065 eq417864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417864 eq418065
  have eq418274 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x X1 x
       have i₂ := eq418116
       grind)
    | exact superpose eq418116 eq16
    | exact resolve eq16 eq418116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419393 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq418274 x X0
       have i₂ := eq418116
       grind)
    | exact superpose eq418116 eq418274
    | exact resolve eq418274 eq418116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418116 eq418274
  have eq419469 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq419393 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419393
  have eq419756 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq85929
       have i₂ := eq419469 sF0
       grind)
    | exact superpose eq419469 eq85929
    | (have j1 := eq419469 y
       grind)
    | exact resolve eq85929 eq419469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85929 eq419469
  have eq419794 : x = (M.op x y) := by grind
  clear eq419756
  have eq419873 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq419794
       grind)
    | exact superpose eq419794 eq22
    | exact resolve eq22 eq419794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq420212 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq86939
       have i₂ := eq419794
       grind)
    | exact superpose eq419794 eq86939
    | exact resolve eq86939 eq419794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86939 eq419794
  have eq420306 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq420212
  have eq420431 : (σ x) = (σ y) := by
    first
    | exact superpose eq419873 eq86913
    | exact resolve eq86913 eq419873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86913
  have eq420432 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq419873 eq20
    | exact resolve eq20 eq419873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419873
  have eq422152 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq420431 eq26
    | exact resolve eq26 eq420431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq424550 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq420306 eq885
    | (have j0 := eq885 (M.op x y)
       grind)
    | exact resolve eq885 eq420306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885 eq420306
  have eq424573 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq424550
  have eq424587 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq424573
    | exact resolve eq424573 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq424573
  have eq424620 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq86970 eq424587
    | exact resolve eq424587 eq86970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86970 eq424587
  have eq424650 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq420431 eq424620
    | exact resolve eq424620 eq420431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420431 eq424620
  have eq427228 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq422152 eq424650
    | exact resolve eq424650 eq422152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422152 eq424650
  have eq427492 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq427228 eq27
    | exact resolve eq27 eq427228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq427228
  have eq427522 : False := by grind
  exact eq427522

/-- `Equation4069`: `x ◇ x = ((x ◇ x) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_x_pxx_pyx_Equation4069 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4069 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4069.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X2) := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq19
  have eq33 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) x X2
       have i₂ := eq9 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq74 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  have eq81 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq33 X0 X2
       grind)
    | (have i₁ := eq33 X0 X2
       have i₂ := eq33 X0 (M.op X0 X0)
       grind)
    | exact superpose eq33 eq33
    | exact resolve eq33 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq92 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq92 x y
       grind)
    | exact superpose eq92 eq16
    | (have j1 := eq92 x y
       grind)
    | exact resolve eq16 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq802 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq246
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq246
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq246
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq246
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq246 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq803 : x = y ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq802
  have eq1043 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = X1 ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq74 X0
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq74 X0
       grind)
    | exact resolve eq12 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1048 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq74 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1049 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1043 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq1056 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1049 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1049
    | exact resolve eq1049 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq1084 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1056 X0 X1
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq1056
    | (have j0 := eq1056 X0 X1
       grind)
    | exact resolve eq1056 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1056
  have eq1088 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1084 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1084
    | (have j0 := eq1084 X0 X1
       grind)
    | exact resolve eq1084 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1824 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1048 (σ X0)
       have i₂ := eq29 X0 (σ X0)
       grind)
    | exact superpose eq29 eq1048
    | exact resolve eq1048 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1048
  have eq1829 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1824 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1824
    | (have j0 := eq1824 X0
       grind)
    | exact resolve eq1824 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1824
  have eq1836 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq1829 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1829
    | (have j0 := eq1829 X0
       grind)
    | exact resolve eq1829 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1829
  have eq1843 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1836 X0
       have j1 := eq1088 X0 x
       grind)
    | (have r₁ := eq1836 X0
       have r₂ := eq1088 X0 X0
       grind)
    | exact resolve eq1836 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088 eq1836
  have eq2032 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1843 (σ X0)
       grind)
    | exact superpose eq1843 eq15
    | exact resolve eq15 eq1843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2038 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq1843 (τ X0)
       grind)
    | exact superpose eq1843 eq35
    | exact resolve eq35 eq1843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq2057 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2038 X0
       have i₂ := eq1843 X0
       grind)
    | exact superpose eq1843 eq2038
    | exact resolve eq2038 eq1843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2038
  have eq2063 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2032 X0
       have i₂ := eq1843 X0
       grind)
    | exact superpose eq1843 eq2032
    | exact resolve eq2032 eq1843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843 eq2032
  have eq2156 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (M.op (M.op (τ (M.op X0 X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (τ X0) X1 X2
       have i₂ := eq2057 X0
       grind)
    | exact superpose eq2057 eq9
    | exact resolve eq9 eq2057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2399 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq2063 X0
       grind)
    | exact superpose eq2063 eq9
    | exact resolve eq9 eq2063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2403 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81 (σ X0) X1 X2
       have i₂ := eq2063 X0
       grind)
    | exact superpose eq2063 eq81
    | exact resolve eq81 eq2063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq2755 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op (M.op X0 X0) (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2156 X0 (τ (M.op X0 X0)) X1
       have i₂ := eq2057 (M.op X0 X0)
       grind)
    | exact superpose eq2057 eq2156
    | exact resolve eq2156 eq2057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057 eq2156
  have eq4323 : ∀ X0 X1 X2 : G, (τ (M.op (σ (M.op X0 X0)) X1)) = (M.op (τ (M.op (M.op (σ (M.op X0 X0)) X1) (M.op (σ (M.op X0 X0)) X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2755 (σ (M.op X0 X0)) X1
       have i₂ := eq2403 X0 (σ (M.op X0 X0)) X2
       grind)
    | (have i₁ := eq2755 (σ (M.op X0 X0)) X1
       have i₂ := eq2403 X0 X1 (σ (M.op X0 X0))
       grind)
    | exact superpose eq2403 eq2755
    | exact resolve eq2755 eq2403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2403 eq2755
  have eq4411 : ∀ X0 X1 X2 : G, (τ (M.op (σ (M.op X0 X0)) X1)) = (M.op (τ (σ (M.op X0 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4323 X0 X1 X2
       have i₂ := eq2399 X0 X1 (M.op (σ (M.op X0 X0)) X1)
       grind)
    | exact superpose eq2399 eq4323
    | exact resolve eq4323 eq2399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2399 eq4323
  have eq4445 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X2) = (τ (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4411 X0 X1 X2
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq4411
    | exact resolve eq4411 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4411
  have eq5176 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X0) X1)) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (M.op (σ (M.op X0 X0)) X2)
       have i₂ := eq4445 X0 X2 X1
       grind)
    | exact superpose eq4445 eq11
    | exact resolve eq11 eq4445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4445
  have eq6535 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) X1)) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2063 (M.op X0 X0)
       have i₂ := eq5176 X0 X1 (σ (M.op X0 X0))
       grind)
    | exact superpose eq5176 eq2063
    | exact resolve eq2063 eq5176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8687 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq803
       grind)
    | exact superpose eq803 eq16
    | exact resolve eq16 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq8688 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq8687
       have r₂ := eq2063 x
       grind)
    | exact resolve eq8687 eq2063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8687
  have eq8689 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq8688
       have i₂ := eq2063 x
       grind)
    | exact superpose eq2063 eq8688
    | exact resolve eq8688 eq2063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8688
  have eq33854 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8689
       grind)
    | exact superpose eq8689 eq10
    | exact resolve eq10 eq8689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8689
  have eq33926 : x = y ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq33854
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq33854
    | exact resolve eq33854 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33854
  have eq34566 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33926
       grind)
    | exact superpose eq33926 eq16
    | exact resolve eq16 eq33926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33926
  have eq34567 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq34566
       have r₂ := eq2063 x
       grind)
    | exact resolve eq34566 eq2063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2063 eq34566
  have eq34598 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq34567
       grind)
    | exact superpose eq34567 eq10
    | exact resolve eq10 eq34567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34567
  have eq34677 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq34598
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq34598
    | exact resolve eq34598 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34598
  have eq34678 : x = (M.op x x) := by grind
  clear eq34677
  have eq35445 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x X1 x
       have i₂ := eq34678
       grind)
    | exact superpose eq34678 eq9
    | exact resolve eq9 eq34678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35498 : ∀ X0 : G, (σ (M.op x x)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq6535 x x
       have i₂ := eq34678
       grind)
    | exact superpose eq34678 eq6535
    | exact resolve eq6535 eq34678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6535
  have eq35524 : ∀ X0 : G, (σ x) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq35498 X0
       have i₂ := eq34678
       grind)
    | exact superpose eq34678 eq35498
    | exact resolve eq35498 eq34678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34678 eq35498
  have eq40159 : ∀ X0 X1 : G, (M.op (σ x) X1) = (σ (M.op (M.op x x) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5176 x X0 X1
       have i₂ := eq35524 x
       grind)
    | exact superpose eq35524 eq5176
    | exact resolve eq5176 eq35524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5176
  have eq40270 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) := by
    intro X1
    first
    | (have i₁ := eq40159 x X1
       have i₂ := eq35445 x x
       grind)
    | exact superpose eq35445 eq40159
    | exact resolve eq40159 eq35445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35445 eq40159
  have eq41500 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq40270 (σ y)
       grind)
    | exact superpose eq40270 eq16
    | exact resolve eq16 eq40270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40270
  have eq41638 : False := by grind
  exact eq41638

/-- `Equation4075`: `x ◇ x = ((x ◇ y) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pyx_pxy_pyx_Equation4075 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4075 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4075.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X1) X2) := by
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
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X1) X1 X2
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X1) X1) ∨ (M.op X0 X0) = (k X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 X1) X1)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq79
       have i₂ := eq73 y x
       grind)
    | exact superpose eq73 eq79
    | (have j1 := eq73 x x
       grind)
    | exact resolve eq79 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq94
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94
    | exact resolve eq94 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq100
    | exact resolve eq100 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq1047 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq101 eq73
    | (have j0 := eq73 x (σ x)
       grind)
    | exact resolve eq73 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq1048 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq1047
    | exact resolve eq1047 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047
  have eq1051 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1048
       have r₂ := eq27
       grind)
    | exact resolve eq1048 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq1184 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1051 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq1051
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq1051
       grind)
    | exact resolve eq13 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051
  have eq1191 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq1184
  have eq1203 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1191 eq49
    | exact resolve eq49 eq1191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq1191
  have eq1207 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq1203
    | exact resolve eq1203 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1203
  have eq1312 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq73 x x
       have i₂ := eq1207
       grind)
    | exact superpose eq1207 eq73
    | (have j0 := eq73 x x
       grind)
    | exact resolve eq73 eq1207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq1313 : x = (M.op x x) := by grind
  clear eq1312
  have eq1418 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq56 x x x
       have i₂ := eq1313
       grind)
    | exact superpose eq1313 eq56
    | exact resolve eq56 eq1313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1420 : ∀ X0 : G, x ≠ (M.op x x) ∨ x = (k X0 (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq69 x x x
       have i₂ := eq1313
       grind)
    | exact superpose eq1313 eq69
    | exact resolve eq69 eq1313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq1423 : ∀ X0 : G, x = (k X0 (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq1420 X0
       grind)
    | (have r₁ := eq1420 X0
       have r₂ := eq1313
       grind)
    | exact resolve eq1420 eq1313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420
  have eq1425 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq1418 X0
       have i₂ := eq1313
       grind)
    | exact superpose eq1313 eq1418
    | exact resolve eq1418 eq1313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1418
  have eq1431 : ∀ X0 : G, x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq1423 X0
       have i₂ := eq1313
       grind)
    | exact superpose eq1313 eq1423
    | exact resolve eq1423 eq1313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313 eq1423
  have eq1526 : x = (M.op x y) := by
    first
    | (have i₁ := eq1425 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1425
    | (have j0 := eq1425 y
       grind)
    | exact resolve eq1425 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1425
  have eq1570 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1526 eq20
    | exact resolve eq20 eq1526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1526
  have eq1593 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1570
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1570
    | exact resolve eq1570 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1570
  have eq1721 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1593 eq26
    | exact resolve eq26 eq1593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1750 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 x
       have i₂ := eq1431 (τ X0)
       grind)
    | exact superpose eq1431 eq34
    | exact resolve eq34 eq1431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1431
  have eq1752 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1750 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1750
    | (have j0 := eq1750 X0
       grind)
    | exact resolve eq1750 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1750
  have eq1758 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1593 eq1752
    | exact resolve eq1752 eq1593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593 eq1752
  have eq1973 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq1758 X0
       have i₂ := eq73 X0 sF1
       grind)
    | exact superpose eq73 eq1758
    | (have j1 := eq73 X0 (σ (M.op x y))
       grind)
    | exact resolve eq1758 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq1758
  have eq2205 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j0 := eq1973 (σ (M.op x y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1973
  have eq2206 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2205
  have eq2237 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq2206 eq56
    | exact resolve eq56 eq2206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq2248 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq2206 eq2237
    | exact resolve eq2237 eq2206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2206 eq2237
  have eq2269 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2248 eq1721
    | exact resolve eq1721 eq2248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1721 eq2248
  have eq2301 : False := by grind
  exact eq2301

/-- `Equation4075`: `x ◇ x = ((x ◇ y) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_pxx_pyx_Equation4075 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4075 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4075.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X1) X2) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq23 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (M.op (M.op (M.op X0 X3) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X0 X3 X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) X1 X2
       have i₂ := eq9 X0 X1 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq63
    | (have j0 := eq63 (σ X0) (σ X1)
       grind)
    | exact resolve eq63 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) X1) ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq63 X1 (τ X0)
       grind)
    | exact superpose eq63 eq18
    | (have j1 := eq63 X1 (τ X0)
       grind)
    | exact resolve eq18 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq128 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 (M.op X0 X1) X1 X2
       have i₂ := eq9 X0 X1 (M.op (M.op X0 X1) X1)
       grind)
    | exact superpose eq9 eq27
    | exact resolve eq27 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq222 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X3) X3) X4) = (k X4 (M.op (M.op X0 X3) X3)) ∨ (M.op (M.op (M.op X0 X1) X1) X2) ≠ (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq12 X4 (M.op (M.op X0 X3) X3)
       have i₂ := eq23 X0 X3 (M.op (M.op X0 X3) X3) X1 X2
       grind)
    | (have i₁ := eq12 X4 (M.op (M.op X0 X3) X3)
       have i₂ := eq23 X0 X1 X2 X3 (M.op (M.op X0 X3) X3)
       grind)
    | exact superpose eq23 eq12
    | (have j0 := eq12 X4 (M.op (M.op X0 X3) X3)
       grind)
    | exact resolve eq12 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq496 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq74 y x
       grind)
    | exact superpose eq74 eq16
    | (have j1 := eq74 y x
       grind)
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq792 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq80 X0 (τ X0)
       grind)
    | exact superpose eq80 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq80 X0 (τ X0)
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq80 X0 (τ X0)
       grind)
    | exact resolve eq12 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq804 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq792 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq806 : ∀ X0 X1 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq804 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq804
    | (have j0 := eq804 X0 X1
       grind)
    | exact resolve eq804 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq815 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq496
       have i₂ := eq63 y x
       grind)
    | exact superpose eq63 eq496
    | (have j1 := eq63 (σ y) (σ x)
       grind)
    | exact resolve eq496 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq818 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq815
  have eq819 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq818
       grind)
    | exact superpose eq818 eq9
    | exact resolve eq9 eq818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1168 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq819 X0
       grind)
    | exact superpose eq819 eq16
    | (have j1 := eq819 X0
       grind)
    | exact resolve eq16 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq1183 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op x x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1168 X0
       have i₂ := eq818
       grind)
    | exact superpose eq818 eq1168
    | exact resolve eq1168 eq818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq1184 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq1183 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq6922 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq806 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq806
    | exact resolve eq806 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq6971 : ∀ X0 X1 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6922 X0 X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq6922
    | (have j0 := eq6922 X0 X1
       grind)
    | exact resolve eq6922 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6922
  have eq6992 : ∀ X0 X1 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq6971 X0 X1
       grind)
    | exact superpose eq6971 eq10
    | (have j1 := eq6971 X0 X1
       grind)
    | exact resolve eq10 eq6971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6971
  have eq7031 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6992 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq6992
    | (have j0 := eq6992 X0 X0
       grind)
    | exact resolve eq6992 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6992
  have eq7085 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7031 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7031
  have eq7086 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7085 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7085
  have eq7138 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq7086 (σ X0)
       grind)
    | exact superpose eq7086 eq15
    | exact resolve eq15 eq7086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7164 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7138 X0
       have i₂ := eq7086 X0
       grind)
    | exact superpose eq7086 eq7138
    | exact resolve eq7138 eq7086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7086 eq7138
  have eq20120 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X0) = (k X0 (M.op x y)) ∨ (M.op x y) ≠ (M.op (M.op (M.op x X1) X1) X2) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq222 x X1 X2 y x
       have i₂ := eq818
       grind)
    | exact superpose eq818 eq222
    | exact resolve eq222 eq818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq20206 : ∀ X0 : G, (M.op x y) ≠ (M.op x x) ∨ (M.op (M.op x y) X0) = (k X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq20120 X0 x x
       have i₂ := eq9 x x x
       grind)
    | exact superpose eq9 eq20120
    | (have j0 := eq20120 X0 x x
       grind)
    | exact resolve eq20120 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20120
  have eq20274 : ∀ X0 : G, (M.op (M.op x y) X0) = (k X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq20206 X0
       grind)
    | (have r₁ := eq20206 X0
       have r₂ := eq1184 y
       grind)
    | exact resolve eq20206 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184 eq20206
  have eq2334267 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq20274 X0
       have i₂ := eq818
       grind)
    | exact superpose eq818 eq20274
    | exact resolve eq20274 eq818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818 eq20274
  have eq2334550 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2334267 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2334267
  have eq2334962 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq496
       have i₂ := eq2334550 y
       grind)
    | exact superpose eq2334550 eq496
    | exact resolve eq496 eq2334550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496 eq2334550
  have eq2334963 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2334962
  have eq2334964 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2334963
  have eq2340998 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2334964
       grind)
    | exact superpose eq2334964 eq16
    | exact resolve eq16 eq2334964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2341110 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) (σ y) X0
       have i₂ := eq2334964
       grind)
    | exact superpose eq2334964 eq9
    | exact resolve eq9 eq2334964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2341872 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq2341110 X0
       have i₂ := eq2334964
       grind)
    | exact superpose eq2334964 eq2341110
    | exact resolve eq2341110 eq2334964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341110
  have eq2342252 : ∀ X0 : G, (M.op (σ x) X0) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq2341872 X0
       have i₂ := eq7164 x
       grind)
    | exact superpose eq7164 eq2341872
    | exact resolve eq2341872 eq7164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7164 eq2341872
  have eq2343606 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2342252 (σ y)
       have i₂ := eq2334964
       grind)
    | exact superpose eq2334964 eq2342252
    | exact resolve eq2342252 eq2334964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2334964 eq2342252
  have eq2347576 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2343606
       grind)
    | exact superpose eq2343606 eq10
    | exact resolve eq10 eq2343606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2343606
  have eq2348270 : x = (M.op x x) := by
    first
    | (have i₁ := eq2347576
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2347576
    | exact resolve eq2347576 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2347576
  have eq2349025 : ∀ X0 : G, x = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq128 x x x
       have i₂ := eq2348270
       grind)
    | exact superpose eq2348270 eq128
    | exact resolve eq128 eq2348270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq2349688 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq2349025 X0
       have i₂ := eq2348270
       grind)
    | exact superpose eq2348270 eq2349025
    | exact resolve eq2349025 eq2348270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2348270 eq2349025
  have eq2351079 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2340998
       have i₂ := eq2349688 y
       grind)
    | exact superpose eq2349688 eq2340998
    | exact resolve eq2340998 eq2349688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2340998 eq2349688
  have eq2351794 : False := by grind
  exact eq2351794

/-- `Equation4075`: `x ◇ x = ((x ◇ y) ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pyy_pyx_Equation4075 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4075 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4075.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X1) X2) := by
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X0) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X1) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op x y) y) X0) := by
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
  have eq59 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X1) X1 X2
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq56 X0 x X2 X3
       have i₂ := eq14 X0 x (M.op (M.op X0 x) x)
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq73 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq91
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq91
    | (have j1 := eq11 (M.op x x) x
       grind)
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = y := by
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
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq104
    | exact resolve eq104 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq120 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq123 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by grind
  clear eq120
  have eq124 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq123
  have eq213 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq467 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 (σ X0) X2 x
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq61
    | exact resolve eq61 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq533 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X2) X4) (M.op (M.op X0 X2) X4)) = (M.op (M.op (M.op X0 X0) X1) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq59 (M.op X0 X2) X4 X3
       have i₂ := eq59 X0 X2 X1
       grind)
    | (have i₁ := eq59 (M.op X0 X0) X1 X2
       have i₂ := eq59 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq59 eq59
    | exact resolve eq59 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq544 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X1) (M.op x X1)) := by
    intro X1
    first
    | (have i₁ := eq59 x X1 x
       have i₂ := eq213 x
       grind)
    | exact superpose eq213 eq59
    | exact resolve eq59 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq625 : ∀ X0 X2 X4 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X2) X4) (M.op (M.op X0 X2) X4)) := by
    intro X0 X2 X4
    first
    | (have i₁ := eq533 X0 x X2 x X4
       have i₂ := eq61 X0 x x
       grind)
    | exact superpose eq61 eq533
    | exact resolve eq533 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq533
  have eq11581 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq105 eq11
    | (have j0 := eq11 (M.op (σ x) (σ x)) (σ x)
       grind)
    | exact resolve eq11 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq11582 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq11581
    | exact resolve eq11581 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11581
  have eq11593 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq11582
       have r₂ := eq28
       grind)
    | exact resolve eq11582 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11582
  have eq11599 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq11593 eq73
    | exact resolve eq73 eq11593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11593
  have eq11657 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq29 eq11599
    | exact resolve eq11599 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11599
  have eq11658 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11657
  have eq11686 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq213 X0
       have i₂ := eq11658
       grind)
    | exact superpose eq11658 eq213
    | exact resolve eq213 eq11658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq11709 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq625 x x x
       have i₂ := eq11658
       grind)
    | exact superpose eq11658 eq625
    | exact resolve eq625 eq11658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625 eq11658
  have eq11715 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11709 x
       have i₂ := eq544 x
       grind)
    | (have i₁ := eq11709 y
       have i₂ := eq544 x
       grind)
    | exact superpose eq544 eq11709
    | (have j0 := eq11709 y
       grind)
    | exact resolve eq11709 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544 eq11709
  have eq13648 : ∀ X0 : G, x = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq11686 eq11715
    | exact resolve eq11715 eq11686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11686 eq11715
  have eq13677 : ∀ X0 : G, x = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq13648 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13648
  have eq13741 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13677 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13677
    | (have j0 := eq13677 y
       grind)
    | exact resolve eq13677 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13677
  have eq13819 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13741 eq30
    | exact resolve eq30 eq13741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq13741
  have eq13923 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq13819
    | exact resolve eq13819 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq13819
  have eq13924 : x = (M.op x y) ∨ x = y := by grind
  clear eq13923
  have eq13943 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq13924 eq21
    | exact resolve eq21 eq13924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13945 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq13924 eq57
    | exact resolve eq57 eq13924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq13959 : (σ (M.op x x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq13924 eq124
    | exact resolve eq124 eq13924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq14038 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq13959
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq13959
    | exact resolve eq13959 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13959
  have eq14052 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13945 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13945
    | (have j0 := eq13945 X0
       grind)
    | exact resolve eq13945 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13945
  have eq14054 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq13943
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13943
    | exact resolve eq13943 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13943
  have eq14069 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq14054 eq27
    | exact resolve eq27 eq14054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14054
  have eq14577 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq13924 eq14052
    | exact resolve eq14052 eq13924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13924 eq14052
  have eq14625 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq14577 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14577
  have eq14912 : (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq14625 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14625
    | (have j0 := eq14625 y
       grind)
    | exact resolve eq14625 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14625
  have eq15020 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq52
       have i₂ := eq14912
       grind)
    | exact superpose eq14912 eq52
    | exact resolve eq52 eq14912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq15034 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) X1) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq467 x X1 x
       have i₂ := eq14912
       grind)
    | exact superpose eq14912 eq467
    | exact resolve eq467 eq14912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467 eq14912
  have eq15075 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) X1) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq21 eq15034
    | (have j0 := eq15034 X0 X1
       grind)
    | exact resolve eq15034 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15034
  have eq15084 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq15020
    | exact resolve eq15020 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15020
  have eq15196 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq15084 eq14038
    | exact resolve eq14038 eq15084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14038 eq15084
  have eq15224 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq15196
  have eq18788 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq15224 eq15075
    | exact resolve eq15075 eq15224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15075 eq15224
  have eq18878 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq18788 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18788
  have eq19004 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq18878 eq14069
    | exact resolve eq14069 eq18878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14069 eq18878
  have eq19038 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq19004
  have eq19062 : x = y := by
    first
    | (have r₁ := eq19038
       have r₂ := eq28
       grind)
    | exact resolve eq19038 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19038
  have eq19080 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq19062
       grind)
    | exact superpose eq19062 eq19
    | exact resolve eq19 eq19062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq19081 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq19062
       grind)
    | exact superpose eq19062 eq25
    | exact resolve eq25 eq19062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq19062
  have eq19183 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq19081
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19081
    | exact resolve eq19081 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq19081
  have eq19198 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq19183 eq27
    | exact resolve eq27 eq19183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq19183
  have eq19440 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq19198 eq73
    | exact resolve eq73 eq19198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq19198
  have eq19508 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq19440
       have i₂ := eq19080
       grind)
    | exact superpose eq19080 eq19440
    | exact resolve eq19440 eq19080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19080 eq19440
  have eq19527 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19508 eq15
    | exact resolve eq15 eq19508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19508
  have eq19571 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq19527
    | exact resolve eq19527 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq19527
  have eq19580 : False := by grind
  exact eq19580

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_pyy_x_pyy_pyx_Equation4079 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4079 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
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
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq174 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X0 X4) X5) X6) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq16 X0 X4 X5 X6
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq16 X0 X0 X2 X3
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0 X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 (M.op X0 X1) x x X4
       have i₂ := eq16 X0 X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq16 X0 X1 X2 (M.op (M.op X0 X1) X2)
       have i₂ := eq16 (M.op (M.op X0 X1) X2) X3 X4 X5
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : (σ y) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq36 (M.op y y)
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq36
    | exact resolve eq36 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq191 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq37 (M.op sF0 sF0)
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq37
    | exact resolve eq37 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq192 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq20 eq191
    | exact resolve eq191 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq193 : (σ y) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq190
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq190
    | exact resolve eq190 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq202 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) X2) := by
    intro X2
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq90 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq90
    | exact resolve eq90 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq241 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq29 eq230
    | exact resolve eq230 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq248 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq107 (M.op sF3 sF3)
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq107
    | exact resolve eq107 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq259 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq31 eq248
    | exact resolve eq248 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq377 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq438 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq593 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq438 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq174 (σ X0)
       grind)
    | exact superpose eq174 eq438
    | exact resolve eq438 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq622 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq593 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq593
    | exact resolve eq593 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq788 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq789 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq812 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) ≠ (M.op (M.op (M.op X0 X1) X2) X3) ∨ (M.op (M.op (M.op X0 X1) X2) X3) = X0 ∨ (M.op (M.op (M.op X0 X1) X2) X3) = (k X0 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq12
    | exact resolve eq12 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq819 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op y y) ∨ (k y x) = (M.op x x) := by
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
  have eq820 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq827 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq829 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (k X0 X0) ∨ (M.op (M.op (M.op X0 X1) X2) X3) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq812 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq889 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 X2 X3
       have i₂ := eq827 X0
       grind)
    | exact superpose eq827 eq16
    | (have j1 := eq827 X0
       grind)
    | exact resolve eq16 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq892 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X1) X2) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X0 X2 x
       have i₂ := eq827 X0
       grind)
    | exact superpose eq827 eq16
    | (have j1 := eq827 X0
       grind)
    | exact resolve eq16 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq911 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (k x x) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq202 X0
       have i₂ := eq827 x
       grind)
    | exact superpose eq827 eq202
    | (have j1 := eq827 x
       grind)
    | exact resolve eq202 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq927 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq827 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1048 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X2) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X0 x X2
       have i₂ := eq181 X0 x X1
       grind)
    | (have i₁ := eq181 X0 X0 x
       have i₂ := eq181 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq181 eq181
    | exact resolve eq181 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1087 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ (M.op (M.op X0 X0) X1) ∨ (M.op X0 X2) = (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X2) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 x (M.op X0 X0)
       have i₂ := eq181 X0 X1 x
       grind)
    | (have i₁ := eq12 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq181 X0 X1 x
       grind)
    | exact superpose eq181 eq12
    | (have r₁ := eq12 x (M.op X1 X1)
       have r₂ := eq181 X1 X1 x
       grind)
    | (have r₁ := eq12 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq181 X0 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1090 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X2) (M.op X0 X2)) ∨ (M.op X0 X2) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1087 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq1653 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (k X0 X0) X4) X5) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq175 X0 X1 X2 X3 X0 X4 X5
       have i₂ := eq827 X0
       grind)
    | exact superpose eq827 eq175
    | (have j1 := eq827 X0
       grind)
    | exact resolve eq175 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq3226 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq788
       grind)
    | exact superpose eq788 eq39
    | exact resolve eq39 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3227 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3226
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3226
    | exact resolve eq3226 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3226
  have eq3229 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq3227
    | exact resolve eq3227 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3227
  have eq16543 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X0) = (M.op (M.op (k X0 X0) X4) X5) ∨ (M.op (M.op (M.op X0 X1) X2) X3) = X0 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq183 X0 X1 X2 X3 X4 X5
       have i₂ := eq829 X0 X1 X2 X3
       grind)
    | exact superpose eq829 eq183
    | (have j1 := eq829 X0 X1 X2 X3
       grind)
    | exact resolve eq183 eq829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq16592 : ∀ X0 X1 X2 X3 : G, (k X0 X0) ≠ X0 ∨ (M.op (M.op (M.op X0 X1) X2) X3) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq829 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq19950 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3229 eq789
    | exact resolve eq789 eq3229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19957 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq19950
       have r₂ := eq27
       grind)
    | exact resolve eq19950 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19950
  have eq19969 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19957 eq820
    | (have r₁ := eq820
       have r₂ := eq19957
       grind)
    | exact resolve eq820 eq19957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19957
  have eq20001 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq19969
  have eq20002 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq20001
  have eq20015 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3229 eq20002
    | exact resolve eq20002 eq3229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3229 eq20002
  have eq20020 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq20015
       have r₂ := eq27
       grind)
    | exact resolve eq20015 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20015
  have eq20022 : y = (k y (τ (σ x))) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20020 eq259
    | exact resolve eq259 eq20020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20020
  have eq20060 : y = (k y x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq20022
    | exact resolve eq20022 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20022
  have eq20066 : (M.op x y) = (M.op x x) ∨ y = (k y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq20060
       have r₂ := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq20060
       have r₂ := eq13 y x
       grind)
    | exact resolve eq20060 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20060
  have eq20074 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq819
       have i₂ := eq20066
       grind)
    | exact superpose eq20066 eq819
    | (have r₁ := eq819
       have r₂ := eq20066
       grind)
    | exact resolve eq819 eq20066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20066
  have eq20106 : x = (M.op y y) ∨ (M.op x y) = (k y x) ∨ y = (k y x) := by grind
  clear eq20074
  have eq20119 : (M.op x y) = (k y x) ∨ y = (k y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq20106
       have r₂ := eq13 y x
       grind)
    | exact resolve eq20106 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20106
  have eq20143 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq20119
       grind)
    | exact superpose eq20119 eq39
    | exact resolve eq39 eq20119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20119
  have eq20145 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq20143
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20143
    | exact resolve eq20143 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20143
  have eq20149 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | exact superpose eq20 eq20145
    | exact resolve eq20145 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20145
  have eq20184 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq20149 eq789
    | exact resolve eq789 eq20149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20190 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by
    first
    | (have r₁ := eq20184
       have r₂ := eq27
       grind)
    | exact resolve eq20184 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20184
  have eq21651 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq20190 eq820
    | (have r₁ := eq820
       have r₂ := eq20190
       grind)
    | exact resolve eq820 eq20190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20190
  have eq21684 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k y x) := by grind
  clear eq21651
  have eq21685 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k y x) := by grind
  clear eq21684
  have eq21699 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq20149 eq21685
    | exact resolve eq21685 eq20149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20149 eq21685
  have eq21705 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) := by
    first
    | (have r₁ := eq21699
       have r₂ := eq27
       grind)
    | exact resolve eq21699 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21699
  have eq21707 : y = (k y (τ (σ x))) ∨ y = (k y x) := by
    first
    | exact superpose eq21705 eq259
    | exact resolve eq259 eq21705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259 eq21705
  have eq21746 : y = (k y x) ∨ y = (k y x) := by
    first
    | exact superpose eq29 eq21707
    | exact resolve eq21707 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21707
  have eq21747 : y = (k y x) := by grind
  clear eq21746
  have eq21758 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq788
       have i₂ := eq21747
       grind)
    | exact superpose eq21747 eq788
    | exact resolve eq788 eq21747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq21761 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq21747
       grind)
    | exact superpose eq21747 eq39
    | exact resolve eq39 eq21747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21764 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq21761
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21761
    | exact resolve eq21761 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21761
  have eq21777 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq21764 eq789
    | exact resolve eq789 eq21764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq24303 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq819
       have i₂ := eq21758
       grind)
    | exact superpose eq21758 eq819
    | (have r₁ := eq819
       have r₂ := eq21758
       grind)
    | exact resolve eq819 eq21758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819 eq21758
  have eq24346 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq24303
  have eq24347 : x = (M.op y y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq24346
  have eq24362 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq24347
       have i₂ := eq21747
       grind)
    | exact superpose eq21747 eq24347
    | exact resolve eq24347 eq21747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21747 eq24347
  have eq24363 : x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq24362
  have eq24372 : x = (k y y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq24363
       have i₂ := eq827 y
       grind)
    | exact superpose eq827 eq24363
    | (have j1 := eq827 y
       grind)
    | exact resolve eq24363 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24383 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1048 y X1 x
       have i₂ := eq24363
       grind)
    | exact superpose eq24363 eq1048
    | exact resolve eq1048 eq24363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24386 : x ≠ x ∨ x = y ∨ x = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq24363
       grind)
    | exact superpose eq24363 eq12
    | exact resolve eq12 eq24363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24387 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 y y x x
       have i₂ := eq24363
       grind)
    | exact superpose eq24363 eq16
    | exact resolve eq16 eq24363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24390 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x X0) X1) = (M.op (M.op (M.op (M.op x X0) X1) X2) X3) ∨ y = (M.op x y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177 y y X2 X3 x x
       have i₂ := eq24363
       grind)
    | exact superpose eq24363 eq177
    | exact resolve eq177 eq24363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq24391 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq181 y y x
       have i₂ := eq24363
       grind)
    | exact superpose eq24363 eq181
    | exact resolve eq181 eq24363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq24363
  have eq24406 : x = (k y y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq24386
  have eq24410 : ∀ X0 X1 X3 : G, (M.op (M.op x X0) X1) = (M.op (M.op x x) X3) ∨ y = (M.op x y) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq24390 X0 X1 x X3
       have i₂ := eq16 x X0 X1 x
       grind)
    | exact superpose eq16 eq24390
    | exact resolve eq24390 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24390
  have eq24416 : x = (k y y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq24406 eq24372
    | exact resolve eq24372 eq24406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24372
  have eq24417 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq24410 X0 X1 x
       have i₂ := eq202 x
       grind)
    | exact superpose eq202 eq24410
    | exact resolve eq24410 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq24410
  have eq24421 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24387 eq24417
    | (have j1 := eq24387 y (M.op x y)
       grind)
    | exact resolve eq24417 eq24387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24417
  have eq24430 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq24421
       have i₂ := eq827 sF0
       grind)
    | exact superpose eq827 eq24421
    | (have j1 := eq827 (M.op x y)
       grind)
    | exact resolve eq24421 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24466 : x ≠ x ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24421 eq12
    | exact resolve eq12 eq24421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24421
  have eq24486 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq24466
  have eq24557 : ∀ X0 : G, (k x x) = (M.op x X0) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq24383 X0 x
       have i₂ := eq827 x
       grind)
    | exact superpose eq827 eq24383
    | (have j1 := eq827 x
       grind)
    | exact resolve eq24383 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24615 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq24383 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq24383 X0 y
       grind)
    | exact superpose eq24383 eq18
    | (have j1 := eq24383 y X0
       grind)
    | exact resolve eq18 eq24383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24383
  have eq24697 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq24615 eq24557
    | (have j0 := eq24557 y
       grind)
    | exact resolve eq24557 eq24615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24557
  have eq24707 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24615 eq24697
    | exact resolve eq24697 eq24615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24697
  have eq24740 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ x = (k x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq24615 x
       grind)
    | exact superpose eq24615 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq24615 x
       grind)
    | exact resolve eq13 eq24615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25168 : ∀ X0 X1 X2 : G, (k x x) = (M.op (M.op (M.op x X0) X1) X2) ∨ x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq889 x x X2 x
       have i₂ := eq24391 X0
       grind)
    | (have i₁ := eq889 x X0 X2 x
       have i₂ := eq24391 X0
       grind)
    | exact superpose eq24391 eq889
    | (have j0 := eq889 x X0 X1 X2
       grind)
    | exact resolve eq889 eq24391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889 eq24391
  have eq25230 : ∀ X0 : G, (k x x) = (M.op x x) ∨ x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq25168 X0 x x
       have i₂ := eq16 x X0 x x
       grind)
    | exact superpose eq16 eq25168
    | (have j0 := eq25168 X0 x x
       grind)
    | exact resolve eq25168 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25168
  have eq25250 : ∀ X0 : G, (M.op x y) = (k x x) ∨ x = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq24615 eq25230
    | (have j0 := eq25230 X0
       grind)
    | exact resolve eq25230 eq24615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25230
  have eq25258 : ∀ X0 : G, (M.op x y) = (k x x) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq24707 eq25250
    | exact resolve eq25250 eq24707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25250
  have eq25544 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq24406
       grind)
    | exact superpose eq24406 eq40
    | exact resolve eq40 eq24406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24406
  have eq25549 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25544
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25544
    | exact resolve eq25544 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25544
  have eq25553 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25549
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25549
    | exact resolve eq25549 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25549
  have eq25636 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq24707
       grind)
    | exact superpose eq24707 eq39
    | exact resolve eq39 eq24707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25641 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25636
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25636
    | exact resolve eq25636 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25636
  have eq25645 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq25641
    | exact resolve eq25641 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25641
  have eq25704 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq25553 eq892
    | (have j0 := eq892 (σ y) X1 x
       grind)
    | exact resolve eq892 eq25553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26165 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq21777 eq820
    | (have r₁ := eq820
       have r₂ := eq21777
       grind)
    | exact resolve eq820 eq21777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820 eq21777
  have eq26206 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq26165
  have eq26207 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq26206
  have eq26222 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21764 eq26207
    | exact resolve eq26207 eq21764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26207
  have eq26223 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq26222
  have eq26233 : ∀ X0 : G, (σ x) ≠ X0 ∨ (σ y) = (k (σ y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26223 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq26223
       grind)
    | exact resolve eq13 eq26223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26241 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26223 eq1048
    | exact resolve eq1048 eq26223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26245 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26223 eq12
    | exact resolve eq12 eq26223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26223
  have eq26265 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq26245
  have eq26369 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq26241 X0 sF2
       have i₂ := eq827 sF2
       grind)
    | exact superpose eq827 eq26241
    | (have j1 := eq827 (σ x)
       grind)
    | exact resolve eq26241 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26424 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26241 eq26
    | (have j1 := eq26241 (σ y) X0
       grind)
    | exact resolve eq26 eq26241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26429 : ∀ X0 : G, x = (k x (τ (M.op (σ x) X0))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26241 eq241
    | exact resolve eq241 eq26241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq26442 : ∀ X0 X1 : G, (M.op (σ x) X0) ≠ (M.op (σ x) X1) ∨ (M.op X1 X1) = (σ x) ∨ (M.op (σ x) X0) = (k X1 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26241 eq12
    | (have j0 := eq12 X1 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq26241 X0 (σ x)
       grind)
    | (have r₁ := eq12 X1 (σ x)
       have r₂ := eq26241 (σ x) X1
       grind)
    | exact resolve eq12 eq26241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26492 : ∀ X0 X1 : G, (M.op X1 X1) = (σ x) ∨ (M.op (σ x) X0) = (k X1 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq26442 X0 X1
       grind)
    | (have r₁ := eq26442 X0 X1
       have r₂ := eq26241 X0 X1
       grind)
    | (have r₁ := eq26442 X1 X0
       have r₂ := eq26241 X0 X1
       grind)
    | exact resolve eq26442 eq26241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26241 eq26442
  have eq26503 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26424 eq26369
    | (have j0 := eq26369 (σ y)
       grind)
    | exact resolve eq26369 eq26424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26369
  have eq26508 : ∀ X1 : G, (M.op (σ x) (σ y)) = (k X1 (σ x)) ∨ (M.op X1 X1) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq26424 eq26492
    | (have j0 := eq26492 (σ y) X1
       grind)
    | exact resolve eq26492 eq26424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26492
  have eq26548 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26424 eq827
    | exact resolve eq827 eq26424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26424
  have eq27241 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26265 eq115
    | exact resolve eq115 eq26265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq27256 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq27241
    | exact resolve eq27241 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27241
  have eq27316 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq892 y X1 x
       have i₂ := eq27256
       grind)
    | exact superpose eq27256 eq892
    | (have j0 := eq892 y X1 x
       grind)
    | exact resolve eq892 eq27256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27320 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq24387 eq27316
    | (have j0 := eq27316 X0 X1
       have j1 := eq24387 X0 X1
       grind)
    | exact resolve eq27316 eq24387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24387 eq27316
  have eq28730 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq24416
       grind)
    | exact superpose eq24416 eq40
    | exact resolve eq40 eq24416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq24416
  have eq28738 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq28730
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq28730
    | exact resolve eq28730 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28730
  have eq28743 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq28738
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28738
    | exact resolve eq28738 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28738
  have eq28747 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24615 eq28743
    | exact resolve eq28743 eq24615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24615 eq28743
  have eq28757 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq28747 eq892
    | (have j0 := eq892 (σ y) X1 x
       grind)
    | exact resolve eq892 eq28747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29213 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq24430 eq174
    | exact resolve eq174 eq24430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24430
  have eq29517 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq39 x
       have i₂ := eq25258 X0
       grind)
    | exact superpose eq25258 eq39
    | (have j1 := eq25258 X0
       grind)
    | exact resolve eq39 eq25258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25258
  have eq29526 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq29517 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29517
    | (have j0 := eq29517 X0
       grind)
    | exact resolve eq29517 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29517
  have eq29531 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq29526
    | (have j0 := eq29526 X0
       grind)
    | exact resolve eq29526 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29526
  have eq29599 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26503 eq25645
    | exact resolve eq25645 eq26503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26503
  have eq29616 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq29599
       have r₂ := eq27
       grind)
    | exact resolve eq29599 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29599
  have eq29705 : ∀ X0 : G, (σ x) = (M.op (σ X0) (σ X0)) ∨ (k X0 x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26508 eq59
    | (have j1 := eq26508 (σ X0)
       grind)
    | exact resolve eq59 eq26508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq26508
  have eq30181 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq29213
  have eq30186 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq30181
       have r₂ := eq24486
       grind)
    | exact resolve eq30181 eq24486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24486 eq30181
  have eq30200 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30186 eq41
    | exact resolve eq41 eq30186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq30208 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq30200
    | exact resolve eq30200 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30200
  have eq30212 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq30208
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30208
    | exact resolve eq30208 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30208
  have eq35987 : x = (k x (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29616 eq26429
    | exact resolve eq26429 eq29616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29616
  have eq36023 : x = (k x (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq35987
  have eq36059 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq36023
    | exact resolve eq36023 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36023
  have eq36082 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq24740 x
       grind)
    | (have r₁ := eq36059
       have r₂ := eq24740 x
       grind)
    | (have r₁ := eq36059
       have r₂ := eq24740 y
       grind)
    | exact resolve eq36059 eq24740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24740 eq36059
  have eq36109 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq24707
       have i₂ := eq36082
       grind)
    | exact superpose eq36082 eq24707
    | exact resolve eq24707 eq36082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24707
  have eq36116 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq36082
       grind)
    | exact superpose eq36082 eq39
    | exact resolve eq39 eq36082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq36082
  have eq36131 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq36109
  have eq36147 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq36116
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36116
    | exact resolve eq36116 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36116
  have eq36163 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36131 eq27
    | exact resolve eq27 eq36131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36131
  have eq36198 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36147 eq26548
    | exact resolve eq26548 eq36147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26548 eq36147
  have eq36221 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq36198
  have eq49775 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (σ y) X0) X1) X2) = (M.op (M.op (σ x) X3) X4) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq25553 eq1653
    | (have j0 := eq1653 (σ y) X1 X2 X3 X4 x
       grind)
    | exact resolve eq1653 eq25553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49779 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (σ y) X0) X1) X2) = (M.op (M.op (σ x) X3) X4) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq28747 eq1653
    | (have j0 := eq1653 (σ y) X1 X2 X3 X4 x
       grind)
    | exact resolve eq1653 eq28747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1653
  have eq50227 : ∀ X3 X4 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ x) X3) X4) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X3 X4
    first
    | (have i₁ := eq49779 x x X3 X3 X4
       have i₂ := eq16 sF3 x x X3
       grind)
    | exact superpose eq16 eq49779
    | exact resolve eq49779 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49779
  have eq50231 : ∀ X3 X4 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ x) X3) X4) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    intro X3 X4
    first
    | (have i₁ := eq49775 x x X3 X3 X4
       have i₂ := eq16 sF3 x x X3
       grind)
    | exact superpose eq16 eq49775
    | exact resolve eq49775 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49775
  have eq50497 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28757 eq50227
    | exact resolve eq50227 eq28757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28757 eq50227
  have eq50501 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq25704 eq50231
    | exact resolve eq50231 eq25704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25704 eq50231
  have eq50676 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq50497 eq50501
    | exact resolve eq50501 eq50497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50497 eq50501
  have eq50677 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq50676
  have eq51347 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq50677 eq174
    | exact resolve eq174 eq50677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51388 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq50677
  have eq51447 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq51347 eq25553
    | exact resolve eq25553 eq51347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25553
  have eq51451 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq51347 eq28747
    | exact resolve eq28747 eq51347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28747 eq51347
  have eq51470 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq51451
  have eq51472 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq51447
  have eq51484 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq51470
       have r₂ := eq51388
       grind)
    | exact resolve eq51470 eq51388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51470
  have eq51486 : x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq51472
       have r₂ := eq51388
       grind)
    | exact resolve eq51472 eq51388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51388 eq51472
  have eq51501 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq51484 eq51486
    | exact resolve eq51486 eq51484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51484 eq51486
  have eq51502 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq51501
  have eq51525 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq51502 eq1048
    | exact resolve eq1048 eq51502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51502
  have eq51907 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq51525 eq26
    | (have j1 := eq51525 (σ y) X0
       grind)
    | exact resolve eq26 eq51525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51525
  have eq52143 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq51907 eq174
    | exact resolve eq174 eq51907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq52149 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq51907 eq827
    | exact resolve eq827 eq51907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827 eq51907
  have eq52237 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36221 eq52149
    | exact resolve eq52149 eq36221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36221 eq52149
  have eq53841 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq52237 eq97
    | exact resolve eq97 eq52237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq53849 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq52237 eq25645
    | exact resolve eq25645 eq52237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52237
  have eq53885 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq53849
  have eq53910 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq53885
       have r₂ := eq36163
       grind)
    | exact resolve eq53885 eq36163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36163 eq53885
  have eq53916 : y = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq53841
    | exact resolve eq53841 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53841
  have eq53934 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53910 eq53916
    | exact resolve eq53916 eq53910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53916
  have eq53944 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30186 eq53934
    | exact resolve eq53934 eq30186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30186 eq53934
  have eq53953 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53910 eq53944
    | exact resolve eq53944 eq53910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53910 eq53944
  have eq53954 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq53953
  have eq53968 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53954 eq27
    | exact resolve eq27 eq53954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54014 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53954 eq52143
    | exact resolve eq52143 eq53954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52143 eq53954
  have eq54021 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq54014
  have eq55543 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq54021 eq25645
    | exact resolve eq25645 eq54021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25645
  have eq55550 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq54021 eq29531
    | (have j0 := eq29531 X0
       grind)
    | exact resolve eq29531 eq54021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29531 eq54021
  have eq55569 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq55550 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55550
  have eq55572 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq55543
  have eq55581 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq55569 X0
       grind)
    | (have r₁ := eq55569 X0
       have r₂ := eq53968
       grind)
    | exact resolve eq55569 eq53968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55569
  have eq55585 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq55572
       have r₂ := eq53968
       grind)
    | exact resolve eq55572 eq53968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55572
  have eq55599 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq55585
       grind)
    | exact superpose eq55585 eq24
    | exact resolve eq24 eq55585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55585
  have eq55676 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq55599
    | exact resolve eq55599 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55599
  have eq55918 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq55581 eq192
    | exact resolve eq192 eq55581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq55581
  have eq56086 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq55918
    | exact resolve eq55918 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55918
  have eq56127 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30212 eq56086
    | exact resolve eq56086 eq30212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30212 eq56086
  have eq56152 : y = (M.op x y) := by
    first
    | (have r₁ := eq56127
       have r₂ := eq53968
       grind)
    | exact resolve eq56127 eq53968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53968 eq56127
  have eq56167 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq56152
       grind)
    | exact superpose eq56152 eq18
    | exact resolve eq18 eq56152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq56168 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq56152
       grind)
    | exact superpose eq56152 eq24
    | exact resolve eq24 eq56152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq56171 : (σ y) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq193
       have i₂ := eq56152
       grind)
    | exact superpose eq56152 eq193
    | exact resolve eq193 eq56152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq56237 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq56168 eq20
    | exact resolve eq20 eq56168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56307 : ∀ X0 : G, (τ (k X0 (σ y))) = (k (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq56168 eq377
    | exact resolve eq377 eq56168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq59030 : ∀ X0 X1 X2 X3 X4 : G, (M.op y y) = (M.op (M.op x X0) X1) ∨ y = (M.op (M.op (M.op y X2) X3) X4) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16543 y X2 X3 X4 X0 X1
       have i₂ := eq27256
       grind)
    | exact superpose eq27256 eq16543
    | (have j0 := eq16543 y X2 X3 X4 X4 x
       grind)
    | exact resolve eq16543 eq27256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16543 eq27256
  have eq59329 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ y = (M.op (M.op (M.op y X2) X3) X4) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq59030 X0 X1 X2 X3 X4
       have i₂ := eq56152
       grind)
    | exact superpose eq56152 eq59030
    | (have j0 := eq59030 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq59030 eq56152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59030
  have eq59408 : ∀ X0 X1 : G, y = (M.op y y) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq59329 X0 X1 x x x
       have i₂ := eq16 y x x x
       grind)
    | exact superpose eq16 eq59329
    | (have j0 := eq59329 X0 X1 x x x
       grind)
    | exact resolve eq59329 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59329
  have eq59448 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x X0) X1) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq59408 X0 X1
       have i₂ := eq56152
       grind)
    | exact superpose eq56152 eq59408
    | (have j0 := eq59408 X0 X1
       grind)
    | exact resolve eq59408 eq56152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59408
  have eq59460 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27320 eq59448
    | (have j1 := eq27320 y (M.op x y)
       grind)
    | exact resolve eq59448 eq27320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27320 eq59448
  have eq94208 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ (k X0 x) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq622 X0
       have i₂ := eq29705 X0
       grind)
    | exact superpose eq29705 eq622
    | (have j1 := eq29705 X0
       grind)
    | exact resolve eq622 eq29705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622 eq29705
  have eq94350 : ∀ X0 : G, (k X0 x) = (τ (M.op (σ x) (σ y))) ∨ (k X0 x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq29 eq94208
    | (have j0 := eq94208 X0
       grind)
    | exact resolve eq94208 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94208
  have eq94452 : ∀ X0 X1 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op (τ (M.op (σ x) (σ y))) X0) X1) ∨ x = (M.op x x) ∨ x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq892 x X1 x
       have i₂ := eq94350 x
       grind)
    | exact superpose eq94350 eq892
    | (have j0 := eq892 x X1 x
       have j1 := eq94350 x
       grind)
    | exact resolve eq892 eq94350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq94510 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (τ (M.op (σ x) (σ y))) X0) ∨ x = (M.op x x) ∨ x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq911 X0
       have i₂ := eq94350 x
       grind)
    | exact superpose eq94350 eq911
    | (have j1 := eq94350 x
       grind)
    | exact resolve eq911 eq94350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911 eq94350
  have eq94561 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (τ (M.op (σ x) (σ y))) X0) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq94510 X0
       have j1 := eq927 x
       grind)
    | (have r₁ := eq94510 X0
       have r₂ := eq927 x
       grind)
    | exact resolve eq94510 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94510
  have eq94610 : ∀ X0 X1 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op (τ (M.op (σ x) (σ y))) X0) X1) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have j0 := eq94452 X0 X1
       have j1 := eq927 x
       grind)
    | (have r₁ := eq94452 X0 X1
       have r₂ := eq927 x
       grind)
    | exact resolve eq94452 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94452
  have eq94646 : ∀ X1 : G, (M.op (M.op (M.op x y) (M.op x y)) X1) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq94561 eq94610
    | exact resolve eq94610 eq94561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94561 eq94610
  have eq94663 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq179 eq94646
    | exact resolve eq94646 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94646
  have eq98197 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq59460 eq56171
    | exact resolve eq56171 eq59460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56171 eq59460
  have eq98338 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq98197
    | exact resolve eq98197 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98197
  have eq98364 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq56237 eq98338
    | exact resolve eq98338 eq56237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56237 eq98338
  have eq98375 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq26233 (σ y)
       grind)
    | (have r₁ := eq98364
       have r₂ := eq26233 (σ y)
       grind)
    | exact resolve eq98364 eq26233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26233 eq98364
  have eq98400 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq98375 eq26265
    | exact resolve eq26265 eq98375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26265
  have eq98423 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq98375 eq56307
    | exact resolve eq56307 eq98375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56307
  have eq98438 : ∀ X0 X1 X2 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (M.op (M.op (σ y) X0) X1) X2) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq98375 eq16592
    | (have j0 := eq16592 (σ y) X0 X1 X2
       grind)
    | (have r₁ := eq16592 (σ y) X1 X2 x
       have r₂ := eq98375
       grind)
    | exact resolve eq16592 eq98375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16592 eq98375
  have eq98441 : ∀ X0 X1 X2 : G, (σ y) = (M.op (M.op (M.op (σ y) X0) X1) X2) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq98438 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98438
  have eq98449 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq98400
  have eq98460 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq98441 x x x
       have i₂ := eq16 sF3 x x x
       grind)
    | exact superpose eq16 eq98441
    | exact resolve eq98441 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98441
  have eq98474 : y = (k y (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq98423
    | exact resolve eq98423 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq98423
  have eq98485 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq98449 eq98460
    | exact resolve eq98460 eq98449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98449 eq98460
  have eq98493 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq98474
       have i₂ := eq56152
       grind)
    | exact superpose eq56152 eq98474
    | exact resolve eq98474 eq56152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56152 eq98474
  have eq98822 : x = (k x (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq98485 eq26429
    | exact resolve eq26429 eq98485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26429 eq98485
  have eq98900 : x = (k x (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq98822
  have eq98962 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq29 eq98900
    | exact resolve eq98900 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq98900
  have eq99316 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq98493 eq927
    | (have j0 := eq927 (M.op x y)
       grind)
    | (have r₁ := eq927 (M.op x y)
       have r₂ := eq98493
       grind)
    | exact resolve eq927 eq98493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99330 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq99316
  have eq101499 : x ≠ x ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq927 x
       have i₂ := eq98962
       grind)
    | exact superpose eq98962 eq927
    | (have j0 := eq927 x
       grind)
    | (have r₁ := eq927 x
       have r₂ := eq98962
       grind)
    | exact resolve eq927 eq98962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927 eq98962
  have eq101513 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq101499
  have eq101582 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq99330 eq179
    | exact resolve eq179 eq99330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq101654 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x y) X0) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq99330 eq1090
    | exact resolve eq1090 eq99330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq101675 : x ≠ (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq99330
  have eq101697 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq98493 eq101654
    | (have j0 := eq101654 X0
       grind)
    | exact resolve eq101654 eq98493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98493 eq101654
  have eq101698 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq101697 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101697
  have eq101728 : ∀ X0 : G, x = (M.op (M.op x y) X0) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq101513 eq101582
    | exact resolve eq101582 eq101513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101513 eq101582
  have eq101765 : x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq101698 eq101728
    | (have j0 := eq101728 (M.op x y)
       grind)
    | exact resolve eq101728 eq101698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101698 eq101728
  have eq101787 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq101765
       have r₂ := eq101675
       grind)
    | exact resolve eq101765 eq101675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101675 eq101765
  have eq101903 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq101787 eq1048
    | exact resolve eq1048 eq101787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048 eq101787
  have eq102287 : ∀ X0 : G, (M.op x X0) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq94663
       have i₂ := eq101903 x x
       grind)
    | (have i₁ := eq94663
       have i₂ := eq101903 X0 x
       grind)
    | exact superpose eq101903 eq94663
    | exact resolve eq94663 eq101903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94663
  have eq102291 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq56167
       have i₂ := eq101903 sF0 x
       grind)
    | (have i₁ := eq56167
       have i₂ := eq101903 X0 sF0
       grind)
    | exact superpose eq101903 eq56167
    | (have j1 := eq101903 y X0
       grind)
    | exact resolve eq56167 eq101903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56167 eq101903
  have eq102359 : ∀ X0 : G, (M.op x X0) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq102287 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102287
  have eq102402 : ∀ X0 : G, (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq102291 eq102359
    | (have j0 := eq102359 y
       grind)
    | exact resolve eq102359 eq102291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102359
  have eq102434 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq102291 eq102402
    | (have j0 := eq102402 y
       grind)
    | exact resolve eq102402 eq102291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102291 eq102402
  have eq105135 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq102434 eq14
    | exact resolve eq14 eq102434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102434
  have eq105236 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq105135
    | exact resolve eq105135 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105135
  have eq105260 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq105236
       have r₂ := eq27
       grind)
    | exact resolve eq105236 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105236
  have eq105271 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq105260 eq27
    | exact resolve eq27 eq105260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105260
  have eq105305 : x = (M.op x y) := by
    first
    | (have r₁ := eq105271
       have r₂ := eq55676
       grind)
    | exact resolve eq105271 eq55676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55676 eq105271
  have eq105307 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq105305
       grind)
    | exact superpose eq105305 eq22
    | exact resolve eq22 eq105305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq105305
  have eq105542 : (σ x) = (σ y) := by
    first
    | exact superpose eq105307 eq56168
    | exact resolve eq56168 eq105307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56168
  have eq105543 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq105307 eq20
    | exact resolve eq20 eq105307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq105307
  have eq105992 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq105542 eq26
    | exact resolve eq26 eq105542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq106062 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq105542 eq21764
    | exact resolve eq21764 eq105542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21764 eq105542
  have eq107625 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq105992 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq105992
       grind)
    | exact resolve eq12 eq105992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105992
  have eq107672 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq107625
  have eq107712 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq106062 eq107672
    | exact resolve eq107672 eq106062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106062 eq107672
  have eq107713 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq107712
  have eq107775 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq107713 eq27
    | exact resolve eq27 eq107713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq107713
  have eq107859 : False := by grind
  exact eq107859

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_pxy_y_pxx_pxy_Equation4079 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4079 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) X3) := by
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
  clear eq24 eq35
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
  have eq57 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) X2) X3 X4 X5
       have i₂ := eq14 X0 X1 X2 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0 X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X0) X4) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 (M.op X0 X1) x x X4
       have i₂ := eq14 X0 X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X1) X2) ∨ (k (M.op (M.op X0 X1) X2) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op (M.op X0 X1) X2) X3
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X0 X1) X2) X3
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq78
    | exact resolve eq78 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq82
    | exact resolve eq82 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq86 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq84
    | exact resolve eq84 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq86
    | exact resolve eq86 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq109 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x y) ∨ (k x y) = (M.op x x) := by
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
  have eq110 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) X2) := by
    intro X2
    first
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X1) = (M.op X0 X2) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X2) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X0) x
       have i₂ := eq62 X0 X1 x
       grind)
    | (have i₁ := eq12 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq62 X0 X1 x
       grind)
    | exact superpose eq62 eq12
    | (have r₁ := eq12 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq62 X1 X1 (M.op X1 X1)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) x
       have r₂ := eq62 X0 X0 x
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq515 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X2) (M.op X0 X2)) ∨ (M.op (M.op X0 X0) X1) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq510 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq1415 : ∀ X2 : G, (M.op x x) ≠ (M.op (M.op x y) (M.op x y)) ∨ (k (M.op x x) X2) = X2 := by
    intro X2
    first
    | exact superpose eq60 eq66
    | (have j0 := eq66 x y (M.op x y) x
       grind)
    | exact resolve eq66 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq8306 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq87 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8307 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8306
    | exact resolve eq8306 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8306
  have eq8318 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8307
       have r₂ := eq27
       grind)
    | exact resolve eq8307 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8307
  have eq8320 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8318
    | exact resolve eq8318 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8318
  have eq8322 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8320
    | exact resolve eq8320 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8320
  have eq8325 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8322 eq110
    | (have r₁ := eq110
       have r₂ := eq8322
       grind)
    | exact resolve eq110 eq8322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq8322
  have eq8354 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq8325
  have eq8355 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq8354
  have eq8395 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8355 eq87
    | exact resolve eq87 eq8355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq8355
  have eq8403 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8395
  have eq8405 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8403
       have r₂ := eq27
       grind)
    | exact resolve eq8403 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8403
  have eq8408 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq109
       have i₂ := eq8405
       grind)
    | exact superpose eq8405 eq109
    | (have r₁ := eq109
       have r₂ := eq8405
       grind)
    | exact resolve eq109 eq8405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq8410 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq8405
       grind)
    | exact superpose eq8405 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq8405
       grind)
    | exact resolve eq12 eq8405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8405
  have eq8435 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8410
  have eq8436 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8435
  have eq8437 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8408
  have eq8438 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8437
  have eq8460 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq8436
       grind)
    | exact superpose eq8436 eq43
    | exact resolve eq43 eq8436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq8436
  have eq8477 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq8460
    | exact resolve eq8460 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8460
  have eq8479 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq8438
       grind)
    | exact superpose eq8438 eq44
    | exact resolve eq44 eq8438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq8438
  have eq8493 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq8479
    | exact resolve eq8479 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8479
  have eq8534 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8493 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq8493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8493
  have eq8537 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8534
    | exact resolve eq8534 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8534
  have eq8548 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8537
       have r₂ := eq27
       grind)
    | exact resolve eq8537 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8537
  have eq8550 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8548
    | exact resolve eq8548 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8548
  have eq8552 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8550
    | exact resolve eq8550 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8550
  have eq8553 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8552
  have eq8559 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8553 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq8553
       grind)
    | exact resolve eq12 eq8553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8553
  have eq8584 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq8559
  have eq8585 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8584
  have eq8619 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8585 eq8477
    | exact resolve eq8477 eq8585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8477 eq8585
  have eq8624 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8619
  have eq8626 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8624
       have r₂ := eq27
       grind)
    | exact resolve eq8624 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8624
  have eq8630 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) X0) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq8626 eq61
    | exact resolve eq61 eq8626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq12662 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq8630
    | (have j0 := eq8630 (σ y) X0
       grind)
    | exact resolve eq8630 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8630
  have eq12834 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8626 eq12662
    | exact resolve eq12662 eq8626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12662
  have eq12871 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq12834 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12834
  have eq12971 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12871
    | (have j0 := eq12871 (σ y)
       grind)
    | exact resolve eq12871 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12871
  have eq13110 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12971 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq12971
       grind)
    | exact resolve eq13 eq12971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12971
  have eq13172 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13110
       have r₂ := eq8626
       grind)
    | exact resolve eq13110 eq8626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8626 eq13110
  have eq13406 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13172 eq49
    | exact resolve eq49 eq13172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq13172
  have eq13436 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq13406
    | exact resolve eq13406 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq13406
  have eq13725 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq111 x
       have i₂ := eq13436
       grind)
    | exact superpose eq13436 eq111
    | (have j0 := eq111 x
       grind)
    | exact resolve eq111 eq13436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13436
  have eq13726 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq13725
  have eq13894 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq215 X0
       have i₂ := eq13726
       grind)
    | exact superpose eq13726 eq215
    | exact resolve eq215 eq13726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13900 : ∀ X0 X1 X2 X3 : G, x = (M.op (M.op (M.op (M.op x X0) X1) X2) X3) ∨ x = (M.op x y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 x x X2 X3 x x
       have i₂ := eq13726
       grind)
    | exact superpose eq13726 eq57
    | exact resolve eq57 eq13726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq13726
  have eq13937 : ∀ X3 : G, x = (M.op (M.op x x) X3) ∨ x = (M.op x y) := by
    intro X3
    first
    | (have i₁ := eq13900 x x x X3
       have i₂ := eq14 x x x x
       grind)
    | exact superpose eq14 eq13900
    | exact resolve eq13900 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13900
  have eq13945 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13937 x
       have i₂ := eq215 x
       grind)
    | exact superpose eq215 eq13937
    | exact resolve eq13937 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq13937
  have eq25234 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13894 eq13945
    | exact resolve eq13945 eq13894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13894 eq13945
  have eq25326 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq25234 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25234
  have eq25443 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq25326 y
       grind)
    | exact superpose eq25326 eq18
    | (have j1 := eq25326 y
       grind)
    | exact resolve eq18 eq25326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25326
  have eq25503 : x = (M.op x y) := by grind
  clear eq25443
  have eq25539 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq25503 eq20
    | exact resolve eq20 eq25503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq25542 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq25503 eq60
    | exact resolve eq60 eq25503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq25594 : ∀ X0 : G, (M.op x x) ≠ (M.op x x) ∨ (k (M.op x x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq25503 eq1415
    | (have j0 := eq1415 X0
       grind)
    | exact resolve eq1415 eq25503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415
  have eq25595 : ∀ X0 : G, (k (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq25594 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25594
  have eq25647 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq25539
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25539
    | exact resolve eq25539 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25539
  have eq25664 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq25647 eq26
    | exact resolve eq26 eq25647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq25976 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0 (M.op x x)
       have i₂ := eq25595 (τ X0)
       grind)
    | exact superpose eq25595 eq38
    | exact resolve eq38 eq25595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq25595
  have eq25994 : ∀ X0 : G, (k (σ (M.op x x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25976 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq25976
    | exact resolve eq25976 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25976
  have eq26354 : ∀ X0 : G, (M.op x x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq25542 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25542
    | (have j0 := eq25542 y X0
       grind)
    | exact resolve eq25542 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25542
  have eq26548 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq25503 eq26354
    | exact resolve eq26354 eq25503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26354
  have eq26700 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq26548 y
       grind)
    | exact superpose eq26548 eq18
    | (have j1 := eq26548 y
       grind)
    | exact resolve eq18 eq26548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq26548
  have eq26746 : x = (M.op x x) := by
    first
    | exact superpose eq25503 eq26700
    | exact resolve eq26700 eq25503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25503 eq26700
  have eq26826 : ∀ X0 : G, (k (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25994 X0
       have i₂ := eq26746
       grind)
    | exact superpose eq26746 eq25994
    | exact resolve eq25994 eq26746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25994 eq26746
  have eq26906 : ∀ X0 : G, (k (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq26826 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26826
    | (have j0 := eq26826 X0
       grind)
    | exact resolve eq26826 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq26826
  have eq26924 : ∀ X0 : G, (k (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq25647 eq26906
    | exact resolve eq26906 eq25647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25647 eq26906
  have eq27273 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26924 eq111
    | (have j0 := eq111 (σ (M.op x y))
       grind)
    | exact resolve eq111 eq26924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq27326 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq27273
  have eq27527 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq27326 eq515
    | exact resolve eq515 eq27326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515 eq27326
  have eq27564 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq26924 eq27527
    | (have j0 := eq27527 X0
       grind)
    | exact resolve eq27527 eq26924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26924 eq27527
  have eq27565 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have j0 := eq27564 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27564
  have eq27602 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27565 eq25664
    | exact resolve eq25664 eq27565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25664 eq27565
  have eq27684 : False := by grind
  exact eq27684
