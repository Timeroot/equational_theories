import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4426`: `x ◇ (x ◇ y) = (z ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_x_pyx_Equation4426 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4426 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4426.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X3) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  clear eq36
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
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
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
  clear eq51
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq177 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : (σ y) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq37 (M.op y y)
       have i₂ := eq175 y
       grind)
    | exact superpose eq175 eq37
    | exact resolve eq37 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : (σ y) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq179
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq179
    | exact resolve eq179 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
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
  clear eq108 eq175
  have eq220 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq209
    | exact resolve eq209 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq338 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq429 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq338 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq338
    | exact resolve eq338 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq692 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X4 X4) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq16 x x X4 X5
       have i₂ := eq16 x x X0 X1
       grind)
    | (have i₁ := eq16 (M.op x x) X1 x x
       have i₂ := eq16 X0 X1 x (M.op (M.op x x) X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 x x
       have i₂ := eq16 X2 X3 x x
       grind)
    | (have i₁ := eq16 X0 X1 X2 (M.op (M.op X2 X2) X1)
       have i₂ := eq16 (M.op X2 X2) X1 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq744 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq695 X2 X3 X4 (M.op X4 x)
       have i₂ := eq695 X4 x X0 X1
       grind)
    | (have i₁ := eq695 X2 X3 X4 (M.op X4 x)
       have i₂ := eq695 X0 X1 X4 x
       grind)
    | exact superpose eq695 eq695
    | exact resolve eq695 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq749 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq695 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq695
    | (have j0 := eq695 X0 X1 x y
       grind)
    | exact resolve eq695 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq750 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq695
    | (have j0 := eq695 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq695 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X4) X5) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 X2 (M.op X2 x) X4 X5
       have i₂ := eq695 X2 x X0 X1
       grind)
    | (have i₁ := eq16 X2 (M.op X2 x) X4 X5
       have i₂ := eq695 X0 X1 X2 x
       grind)
    | exact superpose eq695 eq16
    | exact resolve eq16 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq769 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq749 x x
       have i₂ := eq750 x x
       grind)
    | (have i₁ := eq749 (σ x) (σ y)
       have i₂ := eq750 x x
       grind)
    | exact superpose eq750 eq749
    | (have j0 := eq749 (σ x) (σ y)
       have j1 := eq750 x y
       grind)
    | exact resolve eq749 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq771 : ∀ X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq744 x x X2 X3 X4
       have i₂ := eq750 x x
       grind)
    | (have i₁ := eq744 (σ x) (σ y) X2 X3 X4
       have i₂ := eq750 x x
       grind)
    | exact superpose eq750 eq744
    | (have j0 := eq744 (σ x) (σ y) X2 X3 X4
       grind)
    | exact resolve eq744 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq777 : ∀ X4 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X4 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X4
    first
    | (have i₁ := eq771 x x X4
       have i₂ := eq750 x x
       grind)
    | (have i₁ := eq771 (σ x) (σ y) X4
       have i₂ := eq750 x x
       grind)
    | exact superpose eq750 eq771
    | (have j0 := eq771 (σ x) (σ y) X4
       grind)
    | exact resolve eq771 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq809 : ∀ X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X2 X3
    first
    | (have i₁ := eq692 x (M.op (M.op x x) x) X2 X3
       have i₂ := eq750 (M.op x x) x
       grind)
    | exact superpose eq750 eq692
    | exact resolve eq692 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq825 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq777 eq16
    | exact resolve eq16 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq839 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) X2) := by
    intro X2
    first
    | (have i₁ := eq825 x x X2
       have i₂ := eq750 x x
       grind)
    | (have i₁ := eq825 (σ x) (σ y) X2
       have i₂ := eq750 x x
       grind)
    | exact superpose eq750 eq825
    | (have j0 := eq825 (σ x) (σ y) X2
       grind)
    | exact resolve eq825 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq850 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq852 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq855 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op (k X0 X0) X3) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 X2 X0 X3
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq862 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq28
    | (have j0 := eq28 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X1 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq28 X0 (M.op X0 X0)
       have r₂ := eq11 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq867 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) X0) ∨ (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 ∨ (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq777 x
       have i₂ := eq11 (M.op sF2 sF4) x
       grind)
    | exact superpose eq11 eq777
    | (have j1 := eq11 (M.op (σ x) (M.op (σ x) (σ y))) X0
       grind)
    | exact resolve eq777 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq870 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (k X0 (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X0) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 X1 X0
       have i₂ := eq11 X0 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 (M.op X1 X1)
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq883 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq884 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq885 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq884 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884
  have eq896 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op (k X0 X0) X3) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq855 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq910 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k X0 (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X0) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq870 X0 X1 x x
       have i₂ := eq750 x x
       grind)
    | (have i₁ := eq870 X0 X1 (σ x) (σ y)
       have i₂ := eq750 X0 X1
       grind)
    | exact superpose eq750 eq870
    | (have j0 := eq870 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq870 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq913 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) X0) ∨ (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have j0 := eq867 X0
       have j1 := eq28 (M.op (σ x) (M.op (σ x) (σ y))) X0
       grind)
    | (have r₁ := eq867 x
       have r₂ := eq28 (M.op (σ x) (M.op (σ x) (σ y))) x
       grind)
    | (have r₁ := eq867 (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq28 (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq867 (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) X0)
       have r₂ := eq28 X0 (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y))))
       grind)
    | exact resolve eq867 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq918 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq862 X0 X1
       have j1 := eq28 X0 X1
       grind)
    | (have r₁ := eq862 X0 X0
       have r₂ := eq28 X0 X0
       grind)
    | (have r₁ := eq862 X0 X1
       have r₂ := eq28 X0 X1
       grind)
    | (have r₁ := eq862 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq28 X0 (M.op X0 X0)
       grind)
    | exact resolve eq862 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq922 : ∀ X0 X3 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (k X0 X0) X3) ∨ (M.op X0 X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq896 X0 x x X3
       have i₂ := eq750 x x
       grind)
    | (have i₁ := eq896 X0 (σ x) (σ y) X3
       have i₂ := eq750 X0 x
       grind)
    | exact superpose eq750 eq896
    | (have j0 := eq896 X0 (σ x) (σ y) X3
       grind)
    | exact resolve eq896 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq937 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k X0 (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq910 X0 X1
       have i₂ := eq809 X1 X0
       grind)
    | exact superpose eq809 eq910
    | (have j0 := eq910 X0 X1
       grind)
    | exact resolve eq910 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq940 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | (have j0 := eq913 X0
       have j1 := eq13 (M.op (σ x) (M.op (σ x) (σ y))) X0
       grind)
    | (have r₁ := eq913 x
       have r₂ := eq13 (M.op (σ x) (M.op (σ x) (σ y))) x
       grind)
    | (have r₁ := eq913 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y))))
       grind)
    | exact resolve eq913 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq944 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq918 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq918 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq918 (M.op X0 X0) X1
       have r₂ := eq13 X0 (k (M.op X0 X0) X1)
       grind)
    | (have r₁ := eq918 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq918 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq952 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq885 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq885
    | (have j0 := eq885 (σ X0)
       grind)
    | exact resolve eq885 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1007 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq839 eq28
    | (have j0 := eq28 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq28 x (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq839 x
       grind)
    | exact resolve eq28 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq1011 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have j0 := eq1007 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1020 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq1011 eq399
    | exact resolve eq399 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1021 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq1011 eq35
    | exact resolve eq35 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1035 : ∀ X0 : G, (k X0 (σ (M.op (σ x) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1021 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq1021
    | exact resolve eq1021 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq1036 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1020 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1020
    | exact resolve eq1020 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1141 : (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (k (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op x y))) := by
    first
    | exact superpose eq940 eq42
    | exact resolve eq42 eq940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq2173 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq850
       grind)
    | exact superpose eq850 eq40
    | exact resolve eq40 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq2175 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2173
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2173
    | exact resolve eq2173 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2173
  have eq2177 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq2175
    | exact resolve eq2175 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2175
  have eq2208 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (k X0 X0)) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq922 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq922
    | (have j0 := eq922 (σ X0) x
       grind)
    | exact resolve eq922 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4213 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2177 eq852
    | exact resolve eq852 eq2177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4221 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq4213
       have r₂ := eq27
       grind)
    | exact resolve eq4213 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4213
  have eq4226 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq4221 eq220
    | exact resolve eq220 eq4221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq4221
  have eq4275 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq4226
    | exact resolve eq4226 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4226
  have eq4283 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq4275
       have r₂ := eq176
       grind)
    | exact resolve eq4275 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq4275
  have eq4284 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq4283
       have r₂ := eq13 y x
       grind)
    | exact resolve eq4283 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4283
  have eq4288 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq4284
       grind)
    | exact superpose eq4284 eq40
    | exact resolve eq40 eq4284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4284
  have eq4289 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4288
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4288
    | exact resolve eq4288 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4288
  have eq4291 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq4289
       have r₂ := eq177
       grind)
    | exact resolve eq4289 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq4289
  have eq4295 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4291 eq2177
    | exact resolve eq2177 eq4291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2177
  have eq4296 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4291 eq852
    | exact resolve eq852 eq4291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq4329 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq809 y X0
       have i₂ := eq4295
       grind)
    | exact superpose eq4295 eq809
    | exact resolve eq809 eq4295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4373 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4296
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq4296
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq4296 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4391 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq4296 eq809
    | exact resolve eq809 eq4296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4393 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4296 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq4296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4296
  have eq4402 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4393
  have eq4403 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq4373
  have eq4423 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4402 eq4403
    | exact resolve eq4403 eq4402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4402 eq4403
  have eq4525 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq883 (σ X1) (σ X0)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq883
    | (have j0 := eq883 (σ X1) (σ X0)
       grind)
    | exact resolve eq883 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4644 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4329 y
       grind)
    | (have i₁ := eq18
       have i₂ := eq4329 x
       grind)
    | exact superpose eq4329 eq18
    | (have j1 := eq4329 y
       grind)
    | exact resolve eq18 eq4329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4731 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq4644 eq940
    | exact resolve eq940 eq4644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4733 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq4644 eq1011
    | exact resolve eq1011 eq4644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4740 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq4644 eq1035
    | exact resolve eq1035 eq4644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4741 : ∀ X0 : G, (k X0 (τ (M.op x y))) = X0 ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq4644 eq1036
    | exact resolve eq1036 eq4644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4754 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4644 eq1141
    | exact resolve eq1141 eq4644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq4809 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq4754
    | exact resolve eq4754 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4754
  have eq4817 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq20 eq4740
    | (have j0 := eq4740 X0
       grind)
    | exact resolve eq4740 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4740
  have eq5201 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4809 eq883
    | (have j0 := eq883 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq883 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq4809
       grind)
    | exact resolve eq883 eq4809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883 eq4809
  have eq5202 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq5201
  have eq5203 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq5202
  have eq5315 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5203 eq750
    | exact resolve eq750 eq5203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5320 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4644 eq5315
    | exact resolve eq5315 eq4644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5315
  have eq5360 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5320 eq5203
    | exact resolve eq5203 eq5320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5203 eq5320
  have eq5390 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq5360
  have eq5437 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq5390 eq29
    | exact resolve eq29 eq5390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5458 : (M.op x y) ≠ (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  have eq5469 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq5437
    | exact resolve eq5437 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5437
  have eq5850 : (τ (M.op x y)) ≠ (τ (M.op x y)) ∨ (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4741 eq885
    | (have j0 := eq885 (τ (M.op x y))
       grind)
    | (have r₁ := eq885 (τ (M.op x y))
       have r₂ := eq4741 (τ (M.op x y))
       grind)
    | exact resolve eq885 eq4741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4741
  have eq5861 : (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq5850
  have eq5970 : ∀ X0 X1 : G, (k X1 (M.op (σ x) X0)) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq4391 eq1011
    | exact resolve eq1011 eq4391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5977 : ∀ X0 X1 : G, (k X1 (σ (M.op (σ x) X0))) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f5977_14 : ∀ X0 : G, (k X0 (σ (M.op (σ x) (M.op (σ x) (σ y))))) = X0 := by
      intro X0
      grind
    have f5977_15 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f5977_24 : X1 ≠ (k X1 (σ (M.op (σ x) X0))) := by grind
    have f5977_25 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
    have f5977_26 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f5977_28 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      first
      | (have j0 := f5977_15 X0
         grind)
      | (have r₁ := f5977_15 X0
         have r₂ := f5977_25
         grind)
      | exact resolve f5977_15 f5977_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f5977_29 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) X0) := by
      intro X0
      first
      | (have j0 := f5977_28 X0
         grind)
      | (have r₁ := f5977_28 X0
         have r₂ := f5977_26
         grind)
      | exact resolve f5977_28 f5977_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f5977_66 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
      intro X0 X1
      first
      | (have i₁ := f5977_29 X1
         have i₂ := f5977_29 X0
         grind)
      | (have i₁ := f5977_29 X0
         have i₂ := f5977_29 (M.op (σ x) (σ y))
         grind)
      | exact superpose f5977_29 f5977_29
      | exact resolve f5977_29 f5977_29
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f5977_69 : ∀ X0 X1 : G, (k X1 (σ (M.op (σ x) X0))) = X1 := by
      intro X0 X1
      first
      | (have i₁ := f5977_14 X1
         have i₂ := f5977_29 X0
         grind)
      | (have i₁ := f5977_14 X0
         have i₂ := f5977_29 (M.op (σ x) (σ y))
         grind)
      | exact superpose f5977_29 f5977_14
      | exact resolve f5977_14 f5977_29
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f5977_106 : ∀ X0 : G, X1 ≠ (k X1 (σ (M.op (σ x) X0))) := by
      intro X0
      first
      | (have i₁ := f5977_24
         have i₂ := f5977_66 X0 X0
         grind)
      | (have i₁ := f5977_24
         have i₂ := f5977_66 X0 X0
         grind)
      | exact superpose f5977_66 f5977_24
      | exact resolve f5977_24 f5977_66
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f5977_112 : False := by
      first
      | (have r₁ := f5977_106 x
         have r₂ := f5977_69 x X1
         grind)
      | exact resolve f5977_106 f5977_69
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f5977_112
  clear eq1035
  have eq5978 : ∀ X0 X1 : G, (k X1 (τ (M.op (σ x) X0))) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq4391 eq1036
    | exact resolve eq1036 eq4391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7088 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq5970
    | (have j0 := eq5970 (σ y) X0
       grind)
    | exact resolve eq5970 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7337 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7088 eq885
    | (have j0 := eq885 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq885 (M.op (σ x) (σ y))
       have r₂ := eq7088 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq885 eq7088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7340 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7088 eq35
    | exact resolve eq35 eq7088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7088
  have eq7347 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7337
  have eq7354 : ∀ X0 : G, (k X0 (σ (M.op (σ x) (σ y)))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq7340 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq7340
    | exact resolve eq7340 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7340
  have eq7385 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7347 eq750
    | exact resolve eq750 eq7347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7390 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7347 eq7385
    | exact resolve eq7385 eq7347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7347 eq7385
  have eq7478 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7390 eq4391
    | exact resolve eq4391 eq7390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4391
  have eq7495 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq7478 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7478
  have eq7956 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7495 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq7495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7988 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq7956 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7956
  have eq8084 : (σ (M.op (σ x) (σ y))) ≠ (σ (M.op (σ x) (σ y))) ∨ (σ (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (σ y))) (σ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7354 eq885
    | (have j0 := eq885 (σ (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq885 (σ (M.op (σ x) (σ y)))
       have r₂ := eq7354 (σ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq885 eq7354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7354
  have eq8098 : (σ (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (σ y))) (σ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8084
  have eq8669 : ∀ X0 X1 : G, (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 (σ (M.op X1 X1))) ∨ (M.op X1 X1) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 (M.op X1 X1)
       have i₂ := eq937 (τ X0) X1
       grind)
    | exact superpose eq937 eq35
    | (have j1 := eq937 (τ X0) X1
       grind)
    | exact resolve eq35 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq937
  have eq10371 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (τ (M.op x y)) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq5861 eq809
    | exact resolve eq809 eq5861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10397 : ∀ X0 : G, (M.op x y) = (M.op (τ (M.op x y)) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq4644 eq10371
    | exact resolve eq10371 eq4644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10371
  have eq10447 : (M.op x y) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10397 eq5861
    | exact resolve eq5861 eq10397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5861 eq10397
  have eq10501 : (M.op x y) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq10447
  have eq10922 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (σ y))) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq8098 eq809
    | exact resolve eq809 eq8098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10947 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op (σ x) (σ y))) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7390 eq10922
    | exact resolve eq10922 eq7390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10922
  have eq10999 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10947 eq8098
    | exact resolve eq8098 eq10947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8098 eq10947
  have eq11055 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10999
  have eq11134 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11055 eq15
    | exact resolve eq15 eq11055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11055
  have eq16474 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4423 eq116
    | exact resolve eq116 eq4423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq4423
  have eq16488 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq16474
    | exact resolve eq16474 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq16474
  have eq17273 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq16488 eq7495
    | exact resolve eq7495 eq16488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7495 eq16488
  have eq17305 : x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17273
  have eq17354 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq17305
       grind)
    | exact superpose eq17305 eq41
    | exact resolve eq41 eq17305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17356 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op x X0) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq922 y X0
       have i₂ := eq17305
       grind)
    | exact superpose eq17305 eq922
    | (have j0 := eq922 y x
       grind)
    | exact resolve eq922 eq17305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922 eq17305
  have eq17362 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op x X0) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7390 eq17356
    | exact resolve eq17356 eq7390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7390 eq17356
  have eq17363 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17354
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17354
    | exact resolve eq17354 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17354
  have eq17369 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17363
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17363
    | exact resolve eq17363 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17363
  have eq18005 : (k (M.op x y) x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7988 eq132
    | (have j1 := eq7988 (σ (M.op x y))
       grind)
    | exact resolve eq132 eq7988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq18052 : (M.op (σ x) (σ y)) = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11134 eq18005
    | exact resolve eq18005 eq11134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11134 eq18005
  have eq18527 : y = (M.op y y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq17362 y
       grind)
    | exact superpose eq17362 eq18
    | (have j1 := eq17362 y
       grind)
    | exact resolve eq18 eq17362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17362
  have eq18670 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq182
       have i₂ := eq18527
       grind)
    | exact superpose eq18527 eq182
    | exact resolve eq182 eq18527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq18699 : (M.op y y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq750 y y
       have i₂ := eq18527
       grind)
    | exact superpose eq18527 eq750
    | exact resolve eq750 eq18527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18706 : y = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18527 eq18699
    | exact resolve eq18699 eq18527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18527 eq18699
  have eq18729 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18670
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18670
    | exact resolve eq18670 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18670
  have eq18746 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17369 eq18729
    | exact resolve eq18729 eq17369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17369 eq18729
  have eq18980 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18746 eq1011
    | exact resolve eq1011 eq18746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq18988 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (σ y)))) = X0 ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18746 eq1036
    | exact resolve eq1036 eq18746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq19089 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (σ y)))) = X0 ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq18988
    | (have j0 := eq18988 X0
       grind)
    | exact resolve eq18988 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18988
  have eq19097 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq18980
    | (have j0 := eq18980 X0
       grind)
    | exact resolve eq18980 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18980
  have eq19146 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18746 eq19089
    | exact resolve eq19089 eq18746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19089
  have eq19154 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18746 eq19097
    | exact resolve eq19097 eq18746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18746 eq19097
  have eq19182 : ∀ X0 : G, (k X0 y) = X0 ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq32 eq19146
    | exact resolve eq19146 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19146
  have eq19455 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18706 eq5970
    | exact resolve eq5970 eq18706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5970
  have eq19456 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18706 eq5977
    | exact resolve eq5977 eq18706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5977 eq18706
  have eq19492 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq19456 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19456
  have eq19493 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq19455 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19455
  have eq19534 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19492 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19492
    | (have j0 := eq19492 X0
       grind)
    | exact resolve eq19492 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19492
  have eq19535 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq19182 eq19493
    | (have j0 := eq19493 X0
       have j1 := eq19182 X0
       grind)
    | exact resolve eq19493 eq19182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19182 eq19493
  have eq19536 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq19535 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19535
  have eq19636 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq19154 eq19534
    | (have j0 := eq19534 X0
       have j1 := eq19154 X0
       grind)
    | exact resolve eq19534 eq19154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19154 eq19534
  have eq19637 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq19636 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19636
  have eq19714 : y ≠ y ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq885 y
       have i₂ := eq19536 y
       grind)
    | exact superpose eq19536 eq885
    | (have j0 := eq885 y
       grind)
    | (have r₁ := eq885 y
       have r₂ := eq19536 y
       grind)
    | exact resolve eq885 eq19536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19536
  have eq19744 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq19714
  have eq19954 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19637 eq885
    | (have j0 := eq885 (σ y)
       grind)
    | (have r₁ := eq885 (σ y)
       have r₂ := eq19637 (σ y)
       grind)
    | exact resolve eq885 eq19637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19637
  have eq19985 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq19954
  have eq20143 : (M.op y y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq750 y y
       have i₂ := eq19744
       grind)
    | exact superpose eq19744 eq750
    | exact resolve eq750 eq19744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20144 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op X2 (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq764 y y X2 X0 X1
       have i₂ := eq19744
       grind)
    | exact superpose eq19744 eq764
    | exact resolve eq764 eq19744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq20149 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X2 (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | (have i₁ := eq20144 x x X2
       have i₂ := eq809 x x
       grind)
    | exact superpose eq809 eq20144
    | exact resolve eq20144 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20144
  have eq20150 : y = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19744 eq20143
    | exact resolve eq20143 eq19744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20143
  have eq20171 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X2 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq19744 eq20149
    | exact resolve eq20149 eq19744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19744 eq20149
  have eq20178 : ∀ X2 : G, y = (M.op X2 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq20150 eq20171
    | exact resolve eq20171 eq20150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20171
  have eq20214 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19985 eq750
    | exact resolve eq750 eq19985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20223 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19985 eq20214
    | exact resolve eq20214 eq19985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19985 eq20214
  have eq20553 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20178 x
       grind)
    | exact superpose eq20178 eq18
    | (have j1 := eq20178 x
       grind)
    | exact resolve eq18 eq20178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20178
  have eq21191 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq20223 eq695
    | exact resolve eq695 eq20223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20223
  have eq21240 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq21191
    | (have j0 := eq21191 X0 X1
       grind)
    | exact resolve eq21191 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21191
  have eq21271 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21240 x x
       have i₂ := eq750 x x
       grind)
    | (have i₁ := eq21240 (σ x) (σ y)
       have i₂ := eq750 x x
       grind)
    | exact superpose eq750 eq21240
    | (have j0 := eq21240 (σ x) (σ y)
       grind)
    | exact resolve eq21240 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21240
  have eq21278 : y = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20150 eq21271
    | exact resolve eq21271 eq20150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20150 eq21271
  have eq21285 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20553 eq21278
    | exact resolve eq21278 eq20553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20553 eq21278
  have eq21286 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq21285
  have eq21296 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21286 eq27
    | exact resolve eq27 eq21286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31124 : (k (σ (M.op x y)) (σ x)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18052 eq40
    | exact resolve eq40 eq18052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq18052
  have eq31132 : (k (σ (M.op x y)) (σ x)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq31124
    | exact resolve eq31124 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31124
  have eq31137 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21286 eq31132
    | exact resolve eq31132 eq21286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31132
  have eq31142 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq31137
    | exact resolve eq31137 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31137
  have eq31146 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq31142
       have r₂ := eq13 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq31142 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31142
  have eq31149 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq21286 eq31146
    | exact resolve eq31146 eq21286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31146
  have eq31156 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq31149 eq7988
    | (have j0 := eq7988 (σ (M.op x y))
       grind)
    | exact resolve eq7988 eq31149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7988 eq31149
  have eq31159 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by grind
  clear eq31156
  have eq31163 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq31159
       have r₂ := eq27
       grind)
    | exact resolve eq31159 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31159
  have eq31167 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq21286 eq31163
    | exact resolve eq31163 eq21286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31163
  have eq31168 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by grind
  clear eq31167
  have eq31216 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq31168 eq809
    | exact resolve eq809 eq31168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31168
  have eq31240 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq21286 eq31216
    | exact resolve eq31216 eq21286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31216
  have eq31432 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq31240 eq26
    | (have j1 := eq31240 (σ y)
       grind)
    | exact resolve eq26 eq31240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31240
  have eq31724 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq21286 eq31432
    | exact resolve eq31432 eq21286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31432
  have eq31773 : ∀ X0 : G, (k X0 (τ (M.op x y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq31724 eq5978
    | exact resolve eq5978 eq31724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5978
  have eq31807 : ∀ X0 : G, (k X0 (τ (M.op x y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | (have j0 := eq31773 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31773
  have eq31842 : ∀ X0 : G, (k X0 (τ (M.op x y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq21286 eq31807
    | (have j0 := eq31807 X0
       grind)
    | exact resolve eq31807 eq21286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31807
  have eq31843 : ∀ X0 : G, (k X0 (τ (M.op x y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | (have j0 := eq31842 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31842
  have eq33774 : (τ (M.op x y)) ≠ (τ (M.op x y)) ∨ (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq31843 eq885
    | (have j0 := eq885 (τ (M.op x y))
       grind)
    | (have r₁ := eq885 (τ (M.op x y))
       have r₂ := eq31843 (τ (M.op x y))
       grind)
    | exact resolve eq885 eq31843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885 eq31843
  have eq33792 : (τ (M.op x y)) = (M.op (τ (M.op x y)) (τ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by grind
  clear eq33774
  have eq39958 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (τ (M.op x y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq33792 eq809
    | exact resolve eq809 eq33792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq39982 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (M.op (τ (M.op x y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq21286 eq39958
    | exact resolve eq39958 eq21286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21286 eq39958
  have eq40001 : ∀ X0 : G, (M.op x y) = (M.op (τ (M.op x y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq31724 eq39982
    | exact resolve eq39982 eq31724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31724 eq39982
  have eq40066 : (M.op x y) = (τ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq40001 eq33792
    | exact resolve eq33792 eq40001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33792 eq40001
  have eq40149 : (M.op x y) = (τ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by grind
  clear eq40066
  have eq40289 : (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq40149 eq14
    | exact resolve eq14 eq40149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40149
  have eq40315 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq20 eq40289
    | exact resolve eq40289 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40289
  have eq40329 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq40315 eq27
    | exact resolve eq27 eq40315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40315
  have eq60314 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op (τ X0) (τ X0)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq8669 X0 y
       have i₂ := eq4295
       grind)
    | exact superpose eq4295 eq8669
    | exact resolve eq8669 eq4295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4295 eq8669
  have eq60668 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op (τ X0) (τ X0)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq60314 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq60314
    | (have j0 := eq60314 X0
       grind)
    | exact resolve eq60314 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60314
  have eq60783 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ x)) ∨ x = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op (τ X0) (τ X0)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq4644 eq60668
    | (have j0 := eq60668 X0
       grind)
    | exact resolve eq60668 eq4644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60668
  have eq60863 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ x)) ∨ x = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op (τ X0) (τ X0)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq20 eq60783
    | (have j0 := eq60783 X0
       grind)
    | exact resolve eq60783 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60783
  have eq60932 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ x)) ∨ x = (M.op x y) ∨ x = (M.op (τ X0) (τ X0)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq4644 eq60863
    | (have j0 := eq60863 X0
       grind)
    | exact resolve eq60863 eq4644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60863
  have eq60933 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ x)) ∨ x = (M.op x y) ∨ x = (M.op (τ X0) (τ X0)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq60932 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60932
  have eq60984 : ∀ X0 : G, x = (M.op (τ X0) (τ X0)) ∨ x = (M.op x y) ∨ (M.op x y) = (k X0 (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq5390 eq60933
    | (have j0 := eq60933 X0
       grind)
    | exact resolve eq60933 eq5390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5390 eq60933
  have eq169653 : x = (M.op (k x (M.op x y)) (k x (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (k (k (σ x) (σ (M.op x y))) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq100 eq60984
    | (have j0 := eq60984 (k (σ x) (σ (M.op x y)))
       grind)
    | exact resolve eq60984 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq169700 : ∀ X0 : G, x = (k (τ X0) (τ X0)) ∨ x = (M.op x y) ∨ (M.op x y) = (k X0 (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq60984 X0
       have i₂ := eq11 (τ X0) (τ X0)
       grind)
    | exact superpose eq11 eq60984
    | (have j0 := eq60984 X0
       have j1 := eq11 (τ X0) (τ X0)
       grind)
    | exact resolve eq60984 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169773 : ∀ X0 : G, x = (k (τ X0) (τ X0)) ∨ (τ X0) = x ∨ (τ X0) = x ∨ x = (M.op x y) ∨ (M.op x y) = (k X0 (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq11 (τ X0) (τ X0)
       have i₂ := eq60984 X0
       grind)
    | exact superpose eq60984 eq11
    | (have j0 := eq11 y x
       have j1 := eq60984 X0
       grind)
    | exact resolve eq11 eq60984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60984
  have eq169790 : ∀ X0 : G, x = (k (τ X0) (τ X0)) ∨ (τ X0) = x ∨ x = (M.op x y) ∨ (M.op x y) = (k X0 (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq169773 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169773
  have eq169814 : ∀ X0 : G, x = (k (τ X0) (τ X0)) ∨ x = (M.op x y) ∨ (M.op x y) = (k X0 (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq169700 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169700
  have eq169854 : ∀ X0 : G, x = (τ (k X0 X0)) ∨ (τ X0) = x ∨ x = (M.op x y) ∨ (M.op x y) = (k X0 (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq169790 X0
       have i₂ := eq429 X0 X0
       grind)
    | exact superpose eq429 eq169790
    | (have j0 := eq169790 X0
       grind)
    | exact resolve eq169790 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169790
  have eq169887 : ∀ X0 : G, x = (τ (k X0 X0)) ∨ x = (M.op x y) ∨ (M.op x y) = (k X0 (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq169814 X0
       have i₂ := eq429 X0 X0
       grind)
    | exact superpose eq429 eq169814
    | (have j0 := eq169814 X0
       grind)
    | exact resolve eq169814 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429 eq169814
  have eq169900 : x = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (k (k (σ x) (σ (M.op x y))) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4733 eq169653
    | exact resolve eq169653 eq4733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4733 eq169653
  have eq169946 : ∀ X0 : G, x = (τ (k X0 X0)) ∨ x = (M.op x y) ∨ (M.op x y) = (k X0 (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq169854 eq169887
    | (have j0 := eq169887 X0
       have j1 := eq169854 X0
       grind)
    | exact resolve eq169887 eq169854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169854 eq169887
  have eq169956 : x = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (M.op x y) = (k (k (σ x) (σ (M.op x y))) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4329 eq169900
    | exact resolve eq169900 eq4329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169900
  have eq170000 : ∀ X0 : G, x = (τ (k X0 X0)) ∨ x = (M.op x y) ∨ (M.op x y) = (k X0 (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq4329 eq169946
    | (have j0 := eq169946 X0
       grind)
    | exact resolve eq169946 eq4329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4329 eq169946
  have eq170004 : x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k (k (σ x) (σ (M.op x y))) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4644 eq169956
    | exact resolve eq169956 eq4644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169956
  have eq170005 : x = (M.op x y) ∨ (M.op x y) = (k (k (σ x) (σ (M.op x y))) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq170004
  have eq170025 : ∀ X0 : G, x = (τ (k X0 X0)) ∨ x = (M.op x y) ∨ (M.op x y) = (k X0 (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4644 eq170000
    | (have j0 := eq170000 X0
       grind)
    | exact resolve eq170000 eq4644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170000
  have eq170026 : ∀ X0 : G, x = (τ (k X0 X0)) ∨ x = (M.op x y) ∨ (M.op x y) = (k X0 (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq170025 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170025
  have eq170027 : (M.op x y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4817 eq170005
    | exact resolve eq170005 eq4817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4817 eq170005
  have eq170051 : (k x x) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq170027 eq98
    | exact resolve eq98 eq170027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq170110 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10501 eq170051
    | exact resolve eq170051 eq10501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170051
  have eq172874 : x = (τ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq170026 x
       have i₂ := eq170110
       grind)
    | exact superpose eq170110 eq170026
    | (have j0 := eq170026 x
       grind)
    | exact resolve eq170026 eq170110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170110
  have eq172953 : ∀ X0 : G, x = (k X0 (τ (σ X0))) ∨ x = (M.op x y) ∨ (M.op x y) = (k (σ X0) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq399 X0 (σ X0)
       have i₂ := eq170026 (σ X0)
       grind)
    | exact superpose eq170026 eq399
    | (have j1 := eq170026 (σ X0)
       grind)
    | exact resolve eq399 eq170026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399 eq170026
  have eq173023 : x = (τ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (σ x)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq172874
  have eq173137 : ∀ X0 : G, (M.op x y) = (k (σ X0) (σ x)) ∨ x = (M.op x y) ∨ x = (k X0 X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq172953 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq172953
    | (have j0 := eq172953 X0
       grind)
    | exact resolve eq172953 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172953
  have eq173159 : x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10501 eq173023
    | exact resolve eq173023 eq10501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173023
  have eq173160 : (M.op x y) = (k x (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq173159
  have eq174409 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq173160 eq944
    | exact resolve eq944 eq173160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944 eq173160
  have eq174414 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq174409
  have eq179675 : ∀ X0 : G, (k X0 x) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ x = (k X0 X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq173137 eq60
    | (have j1 := eq173137 X0
       grind)
    | exact resolve eq60 eq173137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq173137
  have eq179782 : ∀ X0 : G, (M.op x y) = (k X0 x) ∨ x = (M.op x y) ∨ x = (k X0 X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq10501 eq179675
    | (have j0 := eq179675 X0
       grind)
    | exact resolve eq179675 eq10501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10501 eq179675
  have eq180238 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq179782 y
       grind)
    | (have i₁ := eq37 y
       have i₂ := eq179782 y
       grind)
    | exact superpose eq179782 eq37
    | (have j1 := eq179782 y
       grind)
    | exact resolve eq37 eq179782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq179782
  have eq180330 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq180238
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq180238
    | exact resolve eq180238 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180238
  have eq180442 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4291 eq180330
    | exact resolve eq180330 eq4291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4291 eq180330
  have eq180533 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq180442
    | exact resolve eq180442 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180442
  have eq180534 : x = (k y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq180533
  have eq180897 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq180534
       grind)
    | exact superpose eq180534 eq41
    | exact resolve eq41 eq180534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq180903 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq2208 y X0
       have i₂ := eq180534
       grind)
    | exact superpose eq180534 eq2208
    | (have j0 := eq2208 y x
       grind)
    | exact resolve eq2208 eq180534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2208
  have eq180970 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq180903 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq180903
    | (have j0 := eq180903 X0
       grind)
    | exact resolve eq180903 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180903
  have eq180973 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq180897
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq180897
    | exact resolve eq180897 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180897
  have eq180996 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq180970 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq180970
    | (have j0 := eq180970 X0
       grind)
    | exact resolve eq180970 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq180970
  have eq180998 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq180973
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq180973
    | exact resolve eq180973 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180973
  have eq181008 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq4644 eq180996
    | exact resolve eq180996 eq4644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4644 eq180996
  have eq182520 : ∀ X0 : G, (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq181008 X0
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq181008
    | (have j0 := eq181008 X0
       have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq181008 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182571 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq181008 eq28
    | (have j0 := eq28 (σ y) (σ y)
       have j1 := eq181008 X0
       grind)
    | (have r₁ := eq28 (σ y) (σ y)
       have r₂ := eq181008 X0
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq181008 X0
       grind)
    | exact resolve eq28 eq181008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181008
  have eq182584 : ∀ X0 : G, (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq182571 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182571
  have eq182595 : ∀ X0 : G, (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq182520 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182520
  have eq182612 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq180998 eq182584
    | (have j0 := eq182584 X0
       grind)
    | exact resolve eq182584 eq180998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180998 eq182584
  have eq182641 : ∀ X0 : G, (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq182595 X0
       have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq182595 (σ x)
       have r₂ := eq13 (σ x) (M.op x y)
       grind)
    | (have r₁ := eq182595 X0
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq182595 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182595
  have eq182667 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq182612 eq182641
    | (have j0 := eq182641 X0
       have j1 := eq182612 X0
       grind)
    | exact resolve eq182641 eq182612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182612 eq182641
  have eq182687 : ∀ X0 : G, (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq170027 eq182667
    | (have j0 := eq182667 X0
       grind)
    | exact resolve eq182667 eq170027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170027 eq182667
  have eq182702 : ∀ X0 : G, (M.op x y) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq182687 X0
       grind)
    | (have r₁ := eq182687 X0
       have r₂ := eq174414
       grind)
    | exact resolve eq182687 eq174414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174414 eq182687
  have eq183094 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq182702 eq26
    | (have j1 := eq182702 (σ y)
       grind)
    | exact resolve eq26 eq182702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182702
  have eq183608 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq183094 eq29
    | exact resolve eq29 eq183094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq183094
  have eq183754 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq183608
    | exact resolve eq183608 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq183608
  have eq183791 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq183754 eq27
    | exact resolve eq27 eq183754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183754
  have eq184010 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq183791
       have r₂ := eq5469
       grind)
    | exact resolve eq183791 eq5469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5469 eq183791
  have eq184048 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq184010
       grind)
    | exact superpose eq184010 eq18
    | exact resolve eq18 eq184010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq184144 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq180534
       have i₂ := eq184010
       grind)
    | exact superpose eq184010 eq180534
    | exact resolve eq180534 eq184010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180534 eq184010
  have eq184149 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq184144
  have eq184181 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4731 eq184149
    | exact resolve eq184149 eq4731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4731 eq184149
  have eq184182 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq184181
  have eq184197 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq769 eq184048
    | exact resolve eq184048 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184048
  have eq184413 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq184197 eq777
    | exact resolve eq777 eq184197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq184417 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq184197 eq940
    | exact resolve eq940 eq184197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq185442 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq184417 eq952
    | (have j0 := eq952 (M.op x y)
       grind)
    | exact resolve eq952 eq184417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952 eq184417
  have eq185492 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq185442
  have eq185519 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq185492
    | exact resolve eq185492 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185492
  have eq185534 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq184182 eq185519
    | exact resolve eq185519 eq184182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184182 eq185519
  have eq186584 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq185534 eq750
    | exact resolve eq750 eq185534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq186611 : (M.op x y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq184197 eq186584
    | exact resolve eq186584 eq184197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184197 eq186584
  have eq186712 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq186611 eq185534
    | exact resolve eq185534 eq186611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185534 eq186611
  have eq186776 : (M.op x y) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq186712
  have eq186833 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq186776 eq26
    | exact resolve eq26 eq186776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186891 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq186776 eq5458
    | (have r₁ := eq5458
       have r₂ := eq186776
       grind)
    | exact resolve eq5458 eq186776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5458 eq186776
  have eq187037 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq186891
  have eq187038 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq187037
  have eq187101 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq184413 eq186833
    | exact resolve eq186833 eq184413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184413 eq186833
  have eq187463 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq187101 eq27
    | exact resolve eq27 eq187101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187101
  have eq187674 : x = (M.op x y) := by
    first
    | (have r₁ := eq187463
       have r₂ := eq187038
       grind)
    | exact resolve eq187463 eq187038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187038 eq187463
  have eq187689 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq187674
       grind)
    | exact superpose eq187674 eq22
    | exact resolve eq22 eq187674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq187697 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq769
       have i₂ := eq187674
       grind)
    | exact superpose eq187674 eq769
    | exact resolve eq769 eq187674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769 eq187674
  have eq188487 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq187689 eq20
    | exact resolve eq20 eq187689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187689
  have eq188775 : (σ x) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq188487 eq21296
    | (have r₁ := eq21296
       have r₂ := eq188487
       grind)
    | exact resolve eq21296 eq188487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21296
  have eq188804 : (σ x) ≠ (σ x) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq188487 eq40329
    | (have r₁ := eq40329
       have r₂ := eq188487
       grind)
    | exact resolve eq40329 eq188487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40329
  have eq188815 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ x) := by grind
  clear eq188804
  have eq188821 : (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq188775
  have eq188918 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq188821 eq27
    | exact resolve eq27 eq188821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq189064 : (M.op x y) ≠ (σ x) := by
    first
    | exact superpose eq188487 eq188918
    | exact resolve eq188918 eq188487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188918
  have eq189156 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq188815 eq26
    | exact resolve eq26 eq188815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq188815
  have eq189375 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | (have r₁ := eq189156
       have r₂ := eq189064
       grind)
    | exact resolve eq189156 eq189064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189156
  have eq189402 : (M.op x y) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq188821 eq189375
    | exact resolve eq189375 eq188821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189375
  have eq190115 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq189402 eq695
    | exact resolve eq695 eq189402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190135 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq189402 eq190115
    | exact resolve eq190115 eq189402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190115
  have eq190523 : (M.op (M.op x y) (M.op x y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq188821 eq187697
    | exact resolve eq187697 eq188821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187697 eq188821
  have eq190755 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq189402 eq190523
    | exact resolve eq190523 eq189402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189402 eq190523
  have eq190852 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq190755 eq28
    | (have j0 := eq28 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq28 (M.op x y) (M.op x y)
       have r₂ := eq190755
       grind)
    | exact resolve eq28 eq190755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq190755
  have eq190865 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq190852
  have eq190970 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq190865 eq4525
    | (have j0 := eq4525 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq4525 eq190865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4525 eq190865
  have eq190975 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq190970
  have eq190976 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq190975
  have eq190987 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq190976
    | exact resolve eq190976 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq190976
  have eq190993 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq188487 eq190987
    | exact resolve eq190987 eq188487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188487 eq190987
  have eq192198 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq190993 eq695
    | exact resolve eq695 eq190993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq192230 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq190993 eq192198
    | exact resolve eq192198 eq190993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190993 eq192198
  have eq192284 : (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq192230 x x
       have i₂ := eq190135 x x
       grind)
    | exact superpose eq190135 eq192230
    | exact resolve eq192230 eq190135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190135 eq192230
  have eq192331 : False := by grind
  exact eq192331

/-- `Equation4428`: `x ◇ (x ◇ y) = (z ◇ w) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_y_pyx_x_pyx_Equation4428 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4428 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4428.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X1) := by
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) X1) := by
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
  have eq76 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq36
    | exact resolve eq36 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq81 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq88 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq93 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq81
       grind)
    | exact superpose eq81 eq16
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq88
    | (have j0 := eq88 X0 (σ X1)
       grind)
    | exact resolve eq88 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq80
       have i₂ := eq88 y x
       grind)
    | exact superpose eq88 eq80
    | (have j1 := eq88 x x
       grind)
    | exact resolve eq80 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107
    | exact resolve eq107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq117
    | exact resolve eq117 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq132 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq176 : (σ (k (k y y) y)) = (k (k (σ y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq40 (k y y)
       have i₂ := eq81
       grind)
    | exact superpose eq81 eq40
    | exact resolve eq40 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq81
  have eq210 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq56 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq56
    | (have j0 := eq56 x y
       grind)
    | exact resolve eq56 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 x X2
       have i₂ := eq14 x X2 X0 X1
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x (M.op x y))) := by
    first
    | exact superpose eq210 eq56
    | exact resolve eq56 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq301 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k y (τ X0))
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq397 : (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op x (M.op x y)) = (k (M.op x (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq222 eq13
    | (have r₁ := eq13 (M.op x (M.op x y)) (M.op x y)
       have r₂ := eq222
       grind)
    | exact resolve eq13 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq399 : (M.op x (M.op x y)) = (k (M.op x (M.op x y)) (M.op x y)) := by grind
  clear eq397
  have eq472 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq278 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq278
    | exact resolve eq278 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq683 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq118 eq88
    | (have j0 := eq88 x (σ x)
       grind)
    | exact resolve eq88 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq684 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq683
    | exact resolve eq683 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq687 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq684
       have r₂ := eq27
       grind)
    | exact resolve eq684 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq691 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq687 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq687
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq687
       grind)
    | exact resolve eq13 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq695 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq691
  have eq700 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq695 eq49
    | exact resolve eq49 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq695
  have eq704 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq700
    | exact resolve eq700 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq700
  have eq707 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq88 x x
       have i₂ := eq704
       grind)
    | exact superpose eq704 eq88
    | (have j0 := eq88 x x
       grind)
    | exact resolve eq88 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq708 : x = (M.op x x) := by grind
  clear eq707
  have eq712 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq212 x x X0
       have i₂ := eq708
       grind)
    | exact superpose eq708 eq212
    | exact resolve eq212 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq714 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq708
       grind)
    | exact superpose eq708 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq708
       grind)
    | exact resolve eq13 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq718 : x = (k x x) := by grind
  clear eq714
  have eq724 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq718
       grind)
    | exact superpose eq718 eq43
    | exact resolve eq43 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq718
  have eq728 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq724
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq724
    | exact resolve eq724 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq724
  have eq746 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq728 eq88
    | (have j0 := eq88 x (σ x)
       grind)
    | exact resolve eq88 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq747 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq746
  have eq754 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq747 eq212
    | exact resolve eq212 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq747
  have eq800 : ∀ X0 X1 : G, (M.op (M.op x y) (σ X0)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X1) (σ X0)
       have i₂ := eq100 X0 X1
       grind)
    | exact superpose eq100 eq56
    | (have j1 := eq100 X0 X1
       grind)
    | exact resolve eq56 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq805 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq100 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq856 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq712 eq210
    | exact resolve eq210 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq873 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq856
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq856
    | exact resolve eq856 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq885 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq873 eq399
    | exact resolve eq399 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq899 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq885 eq132
    | exact resolve eq132 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq885
  have eq904 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq899
    | exact resolve eq899 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq1008 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq904 eq88
    | (have j0 := eq88 x (σ (M.op x y))
       grind)
    | exact resolve eq88 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq904
  have eq1009 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq1008
  have eq1035 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq1009 eq56
    | exact resolve eq56 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1043 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq712 eq1035
    | exact resolve eq1035 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035
  have eq1045 : (σ (M.op x y)) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq1009 eq1043
    | exact resolve eq1043 eq1009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009 eq1043
  have eq1393 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq712 eq754
    | exact resolve eq754 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq1532 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq26 eq1393
    | (have j0 := eq1393 (σ y)
       grind)
    | exact resolve eq1393 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1393
  have eq6147 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq805 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq805
    | (have j0 := eq805 (τ X0)
       grind)
    | exact resolve eq805 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq6165 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6147 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6147
    | (have j0 := eq6147 X0
       grind)
    | exact resolve eq6147 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6147
  have eq6173 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6165 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6165
    | (have j0 := eq6165 X0
       grind)
    | exact resolve eq6165 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6165
  have eq8311 : ∀ X0 X1 : G, (M.op (σ X1) (σ (k X0 X1))) = (M.op x (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | exact superpose eq712 eq800
    | (have j0 := eq800 X0 X1
       grind)
    | exact resolve eq800 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712 eq800
  have eq8568 : ∀ X0 X1 : G, (M.op x (σ X0)) = (σ (k (k X0 X1) X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq100 (k X0 X1) X1
       have i₂ := eq8311 X0 X1
       grind)
    | exact superpose eq8311 eq100
    | (have j0 := eq100 X0 X1
       have j1 := eq8311 X0 X1
       grind)
    | exact resolve eq100 eq8311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq8311
  have eq8589 : ∀ X0 X1 : G, (M.op x (σ X0)) = (σ (k (k X0 X1) X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq8568 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8568
  have eq45348 : ∀ X0 : G, (M.op x (σ y)) = (σ (k (τ (k (σ y) X0)) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq8589 y (τ X0)
       have i₂ := eq301 X0
       grind)
    | exact superpose eq301 eq8589
    | (have j0 := eq8589 X0 (τ X0)
       grind)
    | exact resolve eq8589 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq45838 : ∀ X0 : G, (M.op x (σ y)) = (k (k (σ y) X0) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq45348 X0
       have i₂ := eq34 (k sF3 X0) (τ X0)
       grind)
    | exact superpose eq34 eq45348
    | (have j0 := eq45348 X0
       grind)
    | exact resolve eq45348 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45348
  have eq46159 : ∀ X0 : G, (M.op x (σ y)) = (k (k (σ y) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq45838 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq45838
    | (have j0 := eq45838 X0
       grind)
    | exact resolve eq45838 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45838
  have eq46357 : ∀ X0 : G, (M.op x (σ y)) = (k (k (σ y) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq46159 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq46159
    | (have j0 := eq46159 X0
       grind)
    | exact resolve eq46159 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46159
  have eq46437 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (k (σ y) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | exact superpose eq1532 eq46357
    | (have j0 := eq46357 X0
       grind)
    | exact resolve eq46357 eq1532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46357
  have eq46456 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (k (σ y) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq46437 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq46437
    | (have j0 := eq46437 X0
       grind)
    | exact resolve eq46437 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46437
  have eq359718 : ∀ X0 X1 : G, (M.op x (σ (τ X0))) = (σ (k (τ (k X0 X1)) (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8589 (τ X0) (τ X1)
       have i₂ := eq472 X1 X0
       grind)
    | exact superpose eq472 eq8589
    | (have j0 := eq8589 X0 (τ X1)
       grind)
    | exact resolve eq8589 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472 eq8589
  have eq359729 : ∀ X0 X1 : G, (M.op x (σ (τ X0))) = (k (k X0 X1) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq359718 X0 X1
       have i₂ := eq34 (k X0 X1) (τ X1)
       grind)
    | exact superpose eq34 eq359718
    | (have j0 := eq359718 X0 X1
       grind)
    | exact resolve eq359718 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq359718
  have eq359889 : ∀ X0 X1 : G, (k (k X0 X1) X1) = (M.op x (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq359729 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq359729
    | (have j0 := eq359729 X0 X1
       grind)
    | exact resolve eq359729 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359729
  have eq360007 : ∀ X0 X1 : G, (M.op x X0) = (k (k X0 X1) X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq359889 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq359889
    | (have j0 := eq359889 X0 X1
       grind)
    | exact resolve eq359889 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359889
  have eq360090 : ∀ X0 X1 : G, (M.op x X0) = (k (k X0 X1) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq360007 X0 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq360007
    | (have j0 := eq360007 X0 X1
       grind)
    | exact resolve eq360007 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360007
  have eq1281543 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq176
       have i₂ := eq360090 y y
       grind)
    | exact superpose eq360090 eq176
    | (have j1 := eq360090 x y
       grind)
    | exact resolve eq176 eq360090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq360090
  have eq1281693 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1281543
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1281543
    | exact resolve eq1281543 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1281543
  have eq1283504 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1281693
    | exact resolve eq1281693 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281693
  have eq1284602 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1283504 eq46456
    | (have j0 := eq46456 (σ y)
       grind)
    | exact resolve eq46456 eq1283504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46456 eq1283504
  have eq1284659 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1284602
       have r₂ := eq27
       grind)
    | exact resolve eq1284602 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284602
  have eq1284683 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1284659 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq1284659
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq1284659
       grind)
    | exact resolve eq13 eq1284659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284659
  have eq1284776 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1284683
  have eq1285015 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1284776 eq93
    | exact resolve eq93 eq1284776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq1284776
  have eq1285133 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq1285015
    | exact resolve eq1285015 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1285015
  have eq1285137 : y = (M.op y y) := by
    first
    | (have j1 := eq6173 y
       grind)
    | (have r₁ := eq1285133
       have r₂ := eq6173 y
       grind)
    | exact resolve eq1285133 eq6173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6173 eq1285133
  have eq1285146 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq56 y y
       have i₂ := eq1285137
       grind)
    | exact superpose eq1285137 eq56
    | exact resolve eq56 eq1285137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1285276 : (M.op y y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq210 eq1285146
    | exact resolve eq1285146 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq1285146
  have eq1285297 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq873 eq1285276
    | exact resolve eq1285276 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873 eq1285276
  have eq1285311 : y = (M.op x y) := by
    first
    | (have i₁ := eq1285297
       have i₂ := eq1285137
       grind)
    | exact superpose eq1285137 eq1285297
    | exact resolve eq1285297 eq1285137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285137 eq1285297
  have eq1285321 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1285311 eq20
    | exact resolve eq20 eq1285311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1285311
  have eq1286216 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1285321
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1285321
    | exact resolve eq1285321 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1285321
  have eq1286353 : (M.op (σ x) (σ y)) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq1286216 eq1532
    | exact resolve eq1532 eq1286216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1532 eq1286216
  have eq1286698 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1045 eq1286353
    | exact resolve eq1286353 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045 eq1286353
  have eq1286776 : False := by grind
  exact eq1286776

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pxy_y_pxy_Equation443 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X1)))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op X0 (M.op y (M.op y (M.op x y)))) = X0 := by
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
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 (M.op X1 X0))) (M.op X0 (M.op X0 (M.op X1 X0)))) = (k (M.op X0 (M.op X0 (M.op X1 X0))) (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    grind
  have eq65 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = (k (M.op X0 (M.op X0 (M.op X1 X0))) (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X1
       have i₂ := eq14 (M.op X0 (M.op X0 (M.op X1 X0))) X0 X1
       grind)
    | exact superpose eq14 eq64
    | exact resolve eq64 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq112
    | exact resolve eq112 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq669 : (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) = (k (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) (M.op (M.op y (M.op x y)) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq51 eq65
    | exact resolve eq65 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq719 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq93 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq720 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq719 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq23184 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23191 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq23184
    | exact resolve eq23184 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23184
  have eq23202 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq23191
       have r₂ := eq28
       grind)
    | exact resolve eq23191 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23191
  have eq23205 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq23202
  have eq23230 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq23205
    | exact resolve eq23205 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23205
  have eq23237 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23230 eq114
    | exact resolve eq114 eq23230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23230
  have eq23252 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq23237
  have eq23255 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq23252
       have r₂ := eq28
       grind)
    | exact resolve eq23252 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23252
  have eq23539 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq23255 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq23255
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq23255
       grind)
    | exact resolve eq12 eq23255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23255
  have eq23563 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq23539
  have eq30679 : (τ (σ y)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq23563 eq58
    | exact resolve eq58 eq23563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq23563
  have eq30738 : y = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq30679
    | exact resolve eq30679 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30679
  have eq30741 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (k x y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq30738
       have r₂ := eq12 x y
       grind)
    | exact resolve eq30738 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30738
  have eq30743 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ x = (M.op y y) := by grind
  clear eq30741
  have eq30768 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq30743
    | exact resolve eq30743 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30743
  have eq31053 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ y = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30768 eq114
    | exact resolve eq114 eq30768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq30768
  have eq31083 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ y = (k x y) := by grind
  clear eq31053
  have eq31094 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq31083
       have r₂ := eq12 x y
       grind)
    | exact resolve eq31083 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31083
  have eq31099 : y = (k x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq31094
       have r₂ := eq28
       grind)
    | exact resolve eq31094 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31094
  have eq31129 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq31099
       grind)
    | exact superpose eq31099 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq31099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31099
  have eq31137 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq31129
  have eq31145 : x = (M.op y y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq31137
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq31137
    | exact resolve eq31137 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31137
  have eq31519 : (M.op x y) = (k x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq31145
  have eq31544 : (M.op x y) = (k x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq31519
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq31519
    | exact resolve eq31519 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31519
  have eq31852 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq31544
       grind)
    | exact superpose eq31544 eq45
    | exact resolve eq45 eq31544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq31544
  have eq31887 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq31852
    | exact resolve eq31852 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31852
  have eq32286 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31887 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq31887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32297 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq32286
    | exact resolve eq32286 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32286
  have eq32308 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq32297
       have r₂ := eq28
       grind)
    | exact resolve eq32297 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32297
  have eq76128 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq32308
  have eq76153 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq76128
    | exact resolve eq76128 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76128
  have eq95834 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq76153 eq31887
    | exact resolve eq31887 eq76153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31887 eq76153
  have eq95920 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq95834
  have eq95954 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq95920
       have r₂ := eq28
       grind)
    | exact resolve eq95920 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95920
  have eq96631 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ x)))) = X0 ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq95954 eq14
    | exact resolve eq14 eq95954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97285 : ∀ X0 : G, x = (M.op y x) ∨ y = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq96631 eq14
    | exact resolve eq14 eq96631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96631
  have eq97451 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op x x))) = X0 ∨ y = (M.op x y) ∨ (M.op X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq97285 X1
       grind)
    | exact superpose eq97285 eq14
    | (have j1 := eq97285 X1
       grind)
    | exact resolve eq14 eq97285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97285
  have eq104223 : ∀ X0 : G, x = (k x x) ∨ y = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq65 x x
       have i₂ := eq97451 x x
       grind)
    | exact superpose eq97451 eq65
    | (have j1 := eq97451 X0 X0
       grind)
    | exact resolve eq65 eq97451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq97451
  have eq104534 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq720 x
       have i₂ := eq104223 X0
       grind)
    | exact superpose eq104223 eq720
    | (have j0 := eq720 x
       have j1 := eq104223 (σ x)
       grind)
    | exact resolve eq720 eq104223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104223
  have eq104547 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq104534 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104534
  have eq104557 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq104547 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq104547
    | (have j0 := eq104547 (σ x)
       grind)
    | exact resolve eq104547 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104547
  have eq104615 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j0 := eq104557 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104557
  have eq104616 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq104615
  have eq104629 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  have eq104630 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ x)))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq104616 eq14
    | exact resolve eq14 eq104616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104661 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq104629 eq50
    | exact resolve eq50 eq104629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq104629
  have eq105421 : (τ (σ x)) = (k x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq104616 eq104661
    | exact resolve eq104661 eq104616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104616 eq104661
  have eq105617 : (τ (σ x)) = (k x x) ∨ y = (M.op x y) := by grind
  clear eq105421
  have eq105627 : x = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq105617
    | exact resolve eq105617 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105617
  have eq105652 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq105627
       grind)
    | exact superpose eq105627 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq105627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105627
  have eq105663 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq105652
  have eq105699 : ∀ X0 : G, (M.op X0 (M.op x (M.op x x))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq105663
       grind)
    | exact superpose eq105663 eq14
    | exact resolve eq14 eq105663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105663
  have eq107990 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f107990_13 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ x)))) = X0 ∨ y = (M.op x y) := by
      intro X0
      grind
    have f107990_19 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X1)))) = X0 := by
      intro X0 X1 X2
      grind
    have f107990_21 : X0 ≠ (M.op X0 (σ x)) := by grind
    have f107990_22 : y ≠ (M.op x y) := by grind
    have f107990_24 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ x) (σ x)))) = X0 := by
      intro X0
      first
      | (have j0 := f107990_13 X0
         grind)
      | (have r₁ := f107990_13 X0
         have r₂ := f107990_22
         grind)
      | exact resolve f107990_13 f107990_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f107990_30 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
      intro X0
      first
      | (have i₁ := f107990_19 X0 (σ x) (σ x)
         have i₂ := f107990_24 (σ x)
         grind)
      | exact superpose f107990_24 f107990_19
      | exact resolve f107990_19 f107990_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f107990_42 : X0 ≠ X0 := by
      first
      | (have i₁ := f107990_21
         have i₂ := f107990_30 X0
         grind)
      | exact superpose f107990_30 f107990_21
      | (have r₁ := f107990_21
         have r₂ := f107990_30 X0
         grind)
      | exact resolve f107990_21 f107990_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f107990_43 : False := by grind
    exact f107990_43
  clear eq104630
  have eq108240 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq107990 eq95954
    | exact resolve eq95954 eq107990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95954 eq107990
  have eq108243 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq108240
  have eq111877 : ∀ X0 : G, (M.op X0 x) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq105699 x
       grind)
    | exact superpose eq105699 eq14
    | exact resolve eq14 eq105699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105699
  have eq112120 : x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq108243
       have i₂ := eq111877 y
       grind)
    | exact superpose eq111877 eq108243
    | exact resolve eq108243 eq111877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108243
  have eq112128 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq112120
  have eq112188 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq112128 eq30
    | exact resolve eq30 eq112128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq112128
  have eq112503 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq112188
    | exact resolve eq112188 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq112188
  have eq112504 : y = (M.op x y) ∨ x = y := by grind
  clear eq112503
  have eq112507 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq112504 eq51
    | exact resolve eq51 eq112504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq127518 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq112507 y
       grind)
    | exact superpose eq112507 eq14
    | exact resolve eq14 eq112507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112507
  have eq127678 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq127518 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq127518
    | (have j0 := eq127518 x
       grind)
    | exact resolve eq127518 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127518
  have eq128014 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq127678 eq112504
    | exact resolve eq112504 eq127678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112504 eq127678
  have eq128041 : x = y := by grind
  clear eq128014
  have eq128182 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq128041
       grind)
    | exact superpose eq128041 eq19
    | exact resolve eq19 eq128041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq128183 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq128041
       grind)
    | exact superpose eq128041 eq25
    | exact resolve eq25 eq128041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq128616 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq128183
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq128183
    | exact resolve eq128183 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128183
  have eq128618 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq128616 eq27
    | exact resolve eq27 eq128616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq128616
  have eq129103 : x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq111877 x
       have i₂ := eq128182
       grind)
    | exact superpose eq128182 eq111877
    | exact resolve eq111877 eq128182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111877
  have eq129129 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq129103
       have i₂ := eq128041
       grind)
    | exact superpose eq128041 eq129103
    | exact resolve eq129103 eq128041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129103
  have eq129130 : x = (M.op x y) := by grind
  clear eq129129
  have eq129149 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq129130 eq21
    | exact resolve eq21 eq129130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq129225 : (M.op (M.op y x) (M.op y x)) = (k (M.op (M.op y x) (M.op y x)) (M.op (M.op y x) (M.op y x))) := by
    first
    | exact superpose eq129130 eq669
    | exact resolve eq669 eq129130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq129439 : (M.op (M.op x x) (M.op x x)) = (k (M.op (M.op x x) (M.op x x)) (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq129225
       have i₂ := eq128041
       grind)
    | exact superpose eq128041 eq129225
    | exact resolve eq129225 eq128041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128041 eq129225
  have eq129515 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq129149
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq129149
    | exact resolve eq129149 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129149
  have eq129553 : (M.op (M.op x y) (M.op x y)) = (k (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq129439
       have i₂ := eq128182
       grind)
    | exact superpose eq128182 eq129439
    | exact resolve eq129439 eq128182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129439
  have eq129630 : (M.op x x) = (k (M.op x x) (M.op x x)) := by
    first
    | exact superpose eq129130 eq129553
    | exact resolve eq129553 eq129130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129553
  have eq129679 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq129630
       have i₂ := eq128182
       grind)
    | exact superpose eq128182 eq129630
    | exact resolve eq129630 eq128182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128182 eq129630
  have eq129693 : x = (k x x) := by
    first
    | exact superpose eq129130 eq129679
    | exact resolve eq129679 eq129130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129130 eq129679
  have eq130605 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq129515 eq128618
    | exact resolve eq128618 eq129515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128618
  have eq130671 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq720 x
       have i₂ := eq129693
       grind)
    | exact superpose eq129693 eq720
    | (have j0 := eq720 x
       grind)
    | exact resolve eq720 eq129693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720 eq129693
  have eq130686 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq130671
  have eq130699 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq130686
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq130686
    | exact resolve eq130686 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq130686
  have eq130725 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq129515 eq130699
    | exact resolve eq130699 eq129515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129515 eq130699
  have eq130747 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq130605 eq130725
    | exact resolve eq130725 eq130605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130605 eq130725
  have eq130767 : False := by grind
  exact eq130767

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_pxy_pyx_Equation443 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X1)))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op X0 (M.op y (M.op y (M.op x y)))) = X0 := by
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
  have eq52 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 (M.op X1 X0)) X0
       have i₂ := eq14 (M.op X0 (M.op X1 X0)) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 (M.op X1 X0))) (M.op X0 (M.op X0 (M.op X1 X0)))) = (k (M.op X0 (M.op X0 (M.op X1 X0))) (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    grind
  have eq65 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = (k (M.op X0 (M.op X0 (M.op X1 X0))) (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X1
       have i₂ := eq14 (M.op X0 (M.op X0 (M.op X1 X0))) X0 X1
       grind)
    | exact superpose eq14 eq64
    | exact resolve eq64 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq89
    | exact resolve eq89 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq103 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq715 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq75 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq75 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq75 X0 X0
       grind)
    | exact resolve eq12 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq722 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq715 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq724 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq722 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq722 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq722 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq722 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq733 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq724 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq724
    | (have j0 := eq724 X0 X1
       grind)
    | exact resolve eq724 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq9239 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9240 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq9239
    | exact resolve eq9239 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9239
  have eq9251 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq9240
       have r₂ := eq28
       grind)
    | exact resolve eq9240 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9240
  have eq9253 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq9251
    | exact resolve eq9251 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9251
  have eq9369 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq9253
  have eq9387 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq9369
    | exact resolve eq9369 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9369
  have eq9395 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq9387 eq97
    | exact resolve eq97 eq9387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9387
  have eq9406 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9395
  have eq9408 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9406
       have r₂ := eq28
       grind)
    | exact resolve eq9406 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9406
  have eq9531 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9408
  have eq9549 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9531
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9531
    | exact resolve eq9531 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9531
  have eq9554 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq9549
       grind)
    | exact superpose eq9549 eq72
    | exact resolve eq72 eq9549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq9549
  have eq9574 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq9554
    | exact resolve eq9554 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9554
  have eq9702 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9574 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq9574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9705 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq9702
    | exact resolve eq9702 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9702
  have eq9716 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9705
       have r₂ := eq28
       grind)
    | exact resolve eq9705 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9705
  have eq9718 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq9716
    | exact resolve eq9716 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9716
  have eq9719 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq9718
  have eq9722 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq9719
  have eq9742 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq9722
    | exact resolve eq9722 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9722
  have eq9758 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9742 eq9574
    | exact resolve eq9574 eq9742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9574 eq9742
  have eq9763 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9758
  have eq9767 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq9763
       have r₂ := eq28
       grind)
    | exact resolve eq9763 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9763
  have eq9770 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9767 eq52
    | exact resolve eq52 eq9767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq9783 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9770 eq65
    | exact resolve eq65 eq9770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9785 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9770 eq14
    | exact resolve eq14 eq9770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9770
  have eq10553 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9783 eq103
    | exact resolve eq103 eq9783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9783
  have eq10589 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq10553
    | exact resolve eq10553 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq10553
  have eq10591 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq9785
    | (have j0 := eq9785 (σ x)
       grind)
    | exact resolve eq9785 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10592 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq9785
  have eq10647 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10591 eq9767
    | exact resolve eq9767 eq10591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9767 eq10591
  have eq10648 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq10647
  have eq10903 : (τ (k (σ x) (σ x))) = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10648 eq94
    | exact resolve eq94 eq10648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq10905 : (τ (k (σ x) (σ x))) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10648 eq103
    | exact resolve eq103 eq10648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq11012 : (k x x) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq50 eq10905
    | exact resolve eq10905 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10905
  have eq11013 : (k x x) = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq50 eq10903
    | exact resolve eq10903 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq10903
  have eq12542 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10648 eq10592
    | exact resolve eq10592 eq10648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10592 eq10648
  have eq12565 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq12542
  have eq13045 : y = (k x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10589
       have i₂ := eq11012
       grind)
    | exact superpose eq11012 eq10589
    | exact resolve eq10589 eq11012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10589 eq11012
  have eq13058 : y = (k x x) ∨ y = (M.op x y) := by grind
  clear eq13045
  have eq13092 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq13058
       grind)
    | exact superpose eq13058 eq44
    | exact resolve eq44 eq13058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq13128 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13092
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13092
    | exact resolve eq13092 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13092
  have eq14475 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12565 eq13128
    | exact resolve eq13128 eq12565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12565 eq13128
  have eq14488 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq14475
  have eq14498 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq14488
  have eq14528 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq14498
    | exact resolve eq14498 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14498
  have eq15291 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14528 eq97
    | exact resolve eq97 eq14528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq14528
  have eq15307 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq15291
  have eq15311 : y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq15307
       have r₂ := eq28
       grind)
    | exact resolve eq15307 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15307
  have eq15538 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq15311
  have eq15568 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15538
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15538
    | exact resolve eq15538 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15538
  have eq15580 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11013
       have i₂ := eq15568
       grind)
    | exact superpose eq15568 eq11013
    | exact resolve eq11013 eq15568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11013 eq15568
  have eq15588 : (M.op x y) = (k x x) ∨ y = (M.op x y) := by grind
  clear eq15580
  have eq15634 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13058
       have i₂ := eq15588
       grind)
    | exact superpose eq15588 eq13058
    | exact resolve eq13058 eq15588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13058 eq15588
  have eq15651 : y = (M.op x y) := by grind
  clear eq15634
  have eq15685 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq15651 eq21
    | exact resolve eq21 eq15651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq15687 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 := by
    intro X0
    first
    | exact superpose eq15651 eq51
    | exact resolve eq51 eq15651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq15799 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq15685
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15685
    | exact resolve eq15685 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15685
  have eq15987 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq15799 eq27
    | exact resolve eq27 eq15799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq16701 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq15687 y
       grind)
    | exact superpose eq15687 eq14
    | exact resolve eq14 eq15687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16703 : y = (k y y) := by
    first
    | (have i₁ := eq65 y y
       have i₂ := eq15687 y
       grind)
    | exact superpose eq15687 eq65
    | exact resolve eq65 eq15687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq15687
  have eq16849 : x = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq16701 x
       grind)
    | exact superpose eq16701 eq19
    | (have j1 := eq16701 x
       grind)
    | exact resolve eq19 eq16701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq16701
  have eq16852 : x = y := by
    first
    | exact superpose eq15651 eq16849
    | exact resolve eq16849 eq15651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15651 eq16849
  have eq16880 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq16852
       grind)
    | exact superpose eq16852 eq25
    | exact resolve eq25 eq16852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq17015 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq15799 eq16880
    | exact resolve eq16880 eq15799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15799 eq16880
  have eq17080 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq17015
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17015
    | exact resolve eq17015 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17015
  have eq17346 : x = (k x x) := by
    first
    | (have i₁ := eq16703
       have i₂ := eq16852
       grind)
    | exact superpose eq16852 eq16703
    | exact resolve eq16703 eq16852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16703 eq16852
  have eq17419 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq733 x x
       have i₂ := eq17346
       grind)
    | exact superpose eq17346 eq733
    | (have j0 := eq733 x x
       grind)
    | exact resolve eq733 eq17346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733 eq17346
  have eq17420 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq17419
  have eq17421 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq17420
  have eq17434 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq17421
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17421
    | exact resolve eq17421 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq17421
  have eq17449 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq17080 eq17434
    | exact resolve eq17434 eq17080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17434
  have eq17586 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y))))) = X0 := by
    intro X0
    first
    | exact superpose eq17449 eq54
    | exact resolve eq54 eq17449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq17613 : ∀ X0 : G, (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) = X0 := by
    intro X0
    first
    | exact superpose eq17449 eq17586
    | exact resolve eq17586 eq17449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17586
  have eq17630 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq17449 eq17613
    | exact resolve eq17613 eq17449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17449 eq17613
  have eq21827 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17630 eq15987
    | exact resolve eq15987 eq17630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15987 eq17630
  have eq21829 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17080 eq21827
    | exact resolve eq21827 eq17080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17080 eq21827
  have eq21859 : False := by grind
  exact eq21859

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_Equation443 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law443 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
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
  have eq58 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq58 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq58 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq58 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq59 (σ X0)
       grind)
    | exact superpose eq59 eq15
    | exact resolve eq15 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq59 (τ X0)
       grind)
    | exact superpose eq59 eq18
    | exact resolve eq18 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq64
    | exact resolve eq64 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq70 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq61
    | exact resolve eq61 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq73 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq67
    | exact resolve eq67 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq67
  have eq84 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq70
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
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq70 X1
       grind)
    | exact superpose eq70 eq95
    | (have j0 := eq95 X0 X1
       grind)
    | exact resolve eq95 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq368 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
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
  have eq401 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq368 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq368
    | (have j0 := eq368 X0 X1
       grind)
    | exact resolve eq368 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq368
  have eq405 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq401 X0 X1
       have j1 := eq84 X1 X0
       grind)
    | (have r₁ := eq401 X0 X0
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq401 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq401
  have eq409 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq405 X0 X1
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq405
    | (have j0 := eq405 X0 X1
       grind)
    | exact resolve eq405 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq1271 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq409 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq409
    | exact resolve eq409 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1287 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq409 (σ X0) X1
       grind)
    | exact superpose eq409 eq15
    | (have j1 := eq409 (σ X0) X1
       grind)
    | exact resolve eq15 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq1298 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1287 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq1287
    | (have j0 := eq1287 X0 X1
       grind)
    | exact resolve eq1287 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287
  have eq1373 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op X0 X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0
       have i₂ := eq1271 X1 (τ X0)
       grind)
    | (have i₁ := eq73 X0
       have i₂ := eq1271 (τ X0) (τ X0)
       grind)
    | exact superpose eq1271 eq73
    | (have j1 := eq1271 X1 (τ X0)
       grind)
    | exact resolve eq73 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1375 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq1271 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq1271 X0 X1
       grind)
    | exact superpose eq1271 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq1271 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq1271 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq1271 X0 X1
       grind)
    | exact resolve eq13 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271
  have eq1451 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1375 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375
  have eq1475 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1451 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq1451 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1451 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451
  have eq1509 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (k X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq1475 X0 (τ X1)
       grind)
    | exact superpose eq1475 eq18
    | (have j1 := eq1475 X0 (τ X1)
       grind)
    | exact resolve eq18 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1523 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1475 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475
  have eq1615 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1523 (σ X0) X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq1523
    | exact resolve eq1523 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523
  have eq19749 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1373 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1373
    | exact resolve eq1373 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373
  have eq19867 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19749 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq19749
    | (have j0 := eq19749 X0 X1
       grind)
    | exact resolve eq19749 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq19749
  have eq22068 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1509 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1509
    | exact resolve eq1509 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1509
  have eq22185 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22068 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq22068
    | (have j0 := eq22068 X0 X1
       grind)
    | exact resolve eq22068 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22068
  have eq38499 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1298 x y
       grind)
    | exact superpose eq1298 eq16
    | (have j1 := eq1298 x y
       grind)
    | exact resolve eq16 eq1298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298
  have eq45430 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq38499
       have i₂ := eq19867 x y
       grind)
    | exact superpose eq19867 eq38499
    | (have j1 := eq19867 x y
       grind)
    | exact resolve eq38499 eq19867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45436 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq38499
       have i₂ := eq22185 y x
       grind)
    | exact superpose eq22185 eq38499
    | (have j1 := eq22185 y x
       grind)
    | (have r₁ := eq38499
       have r₂ := eq22185 y x
       grind)
    | exact resolve eq38499 eq22185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22185
  have eq45437 : (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq45436
  have eq45443 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq45430
  have eq45736 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq38499
       have i₂ := eq45437
       grind)
    | exact superpose eq45437 eq38499
    | exact resolve eq38499 eq45437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38499 eq45437
  have eq45762 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq45736
  have eq45764 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq45762
       have r₂ := eq45443
       grind)
    | exact resolve eq45762 eq45443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45443 eq45762
  have eq46052 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq45764
       grind)
    | exact superpose eq45764 eq16
    | exact resolve eq16 eq45764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46054 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1615 x (σ y)
       have i₂ := eq45764
       grind)
    | exact superpose eq45764 eq1615
    | (have j0 := eq1615 x (σ y)
       grind)
    | (have r₁ := eq1615 x (σ y)
       have r₂ := eq45764
       grind)
    | exact resolve eq1615 eq45764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1615 eq45764
  have eq46135 : (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq46054
  have eq46145 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq46135
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq46135
    | exact resolve eq46135 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46135
  have eq46435 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq46145
       have i₂ := eq19867 x y
       grind)
    | exact superpose eq19867 eq46145
    | (have j1 := eq19867 x y
       grind)
    | exact resolve eq46145 eq19867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19867 eq46145
  have eq46529 : (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq46435
  have eq46611 : False := by grind
  exact eq46611

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation443 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law443 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq2281 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2319 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2281 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2281
  have eq2320 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2319 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319
  have eq2740 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2320 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2320
  have eq2743 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2740 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq2740 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq2740 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq2740 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq2740 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2740
  have eq2843 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq2743 X1 (τ X0)
       grind)
    | exact superpose eq2743 eq19
    | (have j1 := eq2743 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq2743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2846 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2743 (σ X1) (σ X0)
       grind)
    | exact superpose eq2743 eq15
    | (have j1 := eq2743 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq2743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2743
  have eq2993 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2843 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2843
    | exact resolve eq2843 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2843
  have eq3090 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2993 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2993
    | (have j0 := eq2993 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq2993 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2993
  have eq3284 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2846 x y
       grind)
    | exact superpose eq2846 eq16
    | (have j1 := eq2846 x y
       grind)
    | exact resolve eq16 eq2846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2846
  have eq3337 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3284
       have i₂ := eq3090 x y
       grind)
    | exact superpose eq3090 eq3284
    | (have j1 := eq3090 (σ x) (σ y)
       grind)
    | (have r₁ := eq3284
       have r₂ := eq3090 x y
       grind)
    | (have r₁ := eq3284
       have r₂ := eq3090 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq3284
       have r₂ := eq3090 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq3284 eq3090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3090 eq3284
  have eq3338 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq3337
  have eq3342 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3338
       grind)
    | exact superpose eq3338 eq10
    | exact resolve eq10 eq3338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3338
  have eq3386 : x = y ∨ x = y := by
    first
    | (have i₁ := eq3342
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3342
    | exact resolve eq3342 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3342
  have eq3387 : x = y := by grind
  clear eq3386
  have eq3389 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3387
       grind)
    | exact superpose eq3387 eq16
    | exact resolve eq16 eq3387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3387
  have eq3390 : False := by grind
  exact eq3390

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_x_pyx_Equation443 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law443 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq94 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq117 : ∀ X0 X1 : G, (M.op X1 (M.op (τ X0) (M.op (τ X0) (τ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0) (τ X0)
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X0 (M.op X1 X0)))) (M.op (σ (M.op X0 (M.op X0 (M.op X1 X0)))) (σ (M.op X0 (M.op X0 (M.op X1 X0))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47 (M.op X0 (M.op X0 (M.op X1 X0))) X2
       have i₂ := eq9 (M.op X0 (M.op X0 (M.op X1 X0))) X0 X1
       grind)
    | exact superpose eq9 eq47
    | exact resolve eq47 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X0 (M.op X1 X0)))) (σ (M.op (M.op X0 (M.op X0 (M.op X1 X0))) (M.op X0 (M.op X0 (M.op X1 X0))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq132 X0 X1 X2
       have i₂ := eq22 (M.op X0 (M.op X0 (M.op X1 X0)))
       grind)
    | exact superpose eq22 eq132
    | exact resolve eq132 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq155 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X0 (M.op X1 X0)))) (σ (M.op X0 (M.op X0 (M.op X1 X0)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq147 X0 X1 X2
       have i₂ := eq9 (M.op X0 (M.op X0 (M.op X1 X0))) X0 X1
       grind)
    | exact superpose eq9 eq147
    | exact resolve eq147 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq159 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op (M.op X0 (M.op X0 (M.op X1 X0))) (M.op X0 (M.op X0 (M.op X1 X0)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq155 X0 X1 X2
       have i₂ := eq22 (M.op X0 (M.op X0 (M.op X1 X0)))
       grind)
    | exact superpose eq22 eq155
    | exact resolve eq155 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq162 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 (M.op X0 (M.op X1 X0))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq159 X0 X1 X2
       have i₂ := eq9 (M.op X0 (M.op X0 (M.op X1 X0))) X0 X1
       grind)
    | exact superpose eq9 eq159
    | exact resolve eq159 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq173 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (σ (M.op X0 (M.op X0 (M.op X1 X0))))) (M.op (σ (σ (M.op X0 (M.op X0 (M.op X1 X0))))) (σ (σ (M.op X0 (M.op X0 (M.op X1 X0)))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47 (σ (M.op X0 (M.op X0 (M.op X1 X0)))) X2
       have i₂ := eq162 X0 X1 (σ (M.op X0 (M.op X0 (M.op X1 X0))))
       grind)
    | exact superpose eq162 eq47
    | exact resolve eq47 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq178 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (σ (M.op X0 (M.op X0 (M.op X1 X0))))) (σ (M.op (σ (M.op X0 (M.op X0 (M.op X1 X0)))) (σ (M.op X0 (M.op X0 (M.op X1 X0)))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq173 X0 X1 X2
       have i₂ := eq22 (σ (M.op X0 (M.op X0 (M.op X1 X0))))
       grind)
    | exact superpose eq22 eq173
    | exact resolve eq173 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq179 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (σ (M.op X0 (M.op X0 (M.op X1 X0))))) (σ (σ (M.op X0 (M.op X0 (M.op X1 X0))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 X0 X1 X2
       have i₂ := eq162 X0 X1 (σ (M.op X0 (M.op X0 (M.op X1 X0))))
       grind)
    | exact superpose eq162 eq178
    | exact resolve eq178 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq180 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op (σ (M.op X0 (M.op X0 (M.op X1 X0)))) (σ (M.op X0 (M.op X0 (M.op X1 X0))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 X0 X1 X2
       have i₂ := eq22 (σ (M.op X0 (M.op X0 (M.op X1 X0))))
       grind)
    | exact superpose eq22 eq179
    | exact resolve eq179 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq181 : ∀ X0 X1 X2 : G, (M.op X2 (σ (σ (M.op X0 (M.op X0 (M.op X1 X0)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X0 X1 X2
       have i₂ := eq162 X0 X1 (σ (M.op X0 (M.op X0 (M.op X1 X0))))
       grind)
    | exact superpose eq162 eq180
    | exact resolve eq180 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq249 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (τ (M.op X0 (M.op X0 (M.op X1 X0)))) (M.op (τ (M.op X0 (M.op X0 (M.op X1 X0)))) (τ (M.op X0 (M.op X0 (M.op X1 X0))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117 (M.op X0 (M.op X0 (M.op X1 X0))) X2
       have i₂ := eq9 (M.op X0 (M.op X0 (M.op X1 X0))) X0 X1
       grind)
    | exact superpose eq9 eq117
    | exact resolve eq117 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : ∀ X0 X1 : G, (M.op X1 (σ (σ (M.op (M.op (τ X0) (τ (M.op X0 X0))) (M.op (τ X0) (τ (M.op X0 X0))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq181 (M.op (τ X0) (τ (M.op X0 X0))) (τ X0) X1
       have i₂ := eq117 X0 (M.op (τ X0) (τ (M.op X0 X0)))
       grind)
    | exact superpose eq117 eq181
    | exact resolve eq181 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq260 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op (τ X0) (τ (M.op X0 X0))) (M.op (τ X0) (τ (M.op X0 X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq162 (M.op (τ X0) (τ (M.op X0 X0))) (τ X0) X1
       have i₂ := eq117 X0 (M.op (τ X0) (τ (M.op X0 X0)))
       grind)
    | exact superpose eq117 eq162
    | exact resolve eq162 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq280 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (τ (M.op X0 (M.op X0 (M.op X1 X0)))) (τ (M.op (M.op X0 (M.op X0 (M.op X1 X0))) (M.op X0 (M.op X0 (M.op X1 X0))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq249 X0 X1 X2
       have i₂ := eq67 (M.op X0 (M.op X0 (M.op X1 X0)))
       grind)
    | exact superpose eq67 eq249
    | exact resolve eq249 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq292 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (τ (M.op X0 (M.op X0 (M.op X1 X0)))) (τ (M.op X0 (M.op X0 (M.op X1 X0)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq280 X0 X1 X2
       have i₂ := eq9 (M.op X0 (M.op X0 (M.op X1 X0))) X0 X1
       grind)
    | exact superpose eq9 eq280
    | exact resolve eq280 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq300 : ∀ X0 X1 X2 : G, (M.op X2 (τ (M.op (M.op X0 (M.op X0 (M.op X1 X0))) (M.op X0 (M.op X0 (M.op X1 X0)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq292 X0 X1 X2
       have i₂ := eq67 (M.op X0 (M.op X0 (M.op X1 X0)))
       grind)
    | exact superpose eq67 eq292
    | exact resolve eq292 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq307 : ∀ X0 X1 X2 : G, (M.op X2 (τ (M.op X0 (M.op X0 (M.op X1 X0))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq300 X0 X1 X2
       have i₂ := eq9 (M.op X0 (M.op X0 (M.op X1 X0))) X0 X1
       grind)
    | exact superpose eq9 eq300
    | exact resolve eq300 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq320 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq94 x y
       grind)
    | exact superpose eq94 eq16
    | (have j1 := eq94 x y
       grind)
    | exact resolve eq16 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq328 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq94 X1 X0
       grind)
    | exact superpose eq94 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq94 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq94 X0 X1
       grind)
    | exact resolve eq13 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq328 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq332 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq331 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq331
    | (have j0 := eq331 X0 X1
       grind)
    | exact resolve eq331 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq1719 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq320
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq320
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq320
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq320
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq320 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq1720 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1719
  have eq22503 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1720
       grind)
    | exact superpose eq1720 eq16
    | exact resolve eq16 eq1720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1720
  have eq22504 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq22503
       have r₂ := eq22 x
       grind)
    | exact resolve eq22503 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22503
  have eq22506 : x ≠ x ∨ y = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq22504
       grind)
    | exact superpose eq22504 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq22504
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq22504
       grind)
    | exact resolve eq13 eq22504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22541 : x = y ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq22506
  have eq42149 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22541
       grind)
    | exact superpose eq22541 eq16
    | exact resolve eq16 eq22541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22541
  have eq42150 : y = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq42149
       have r₂ := eq22 x
       grind)
    | exact resolve eq42149 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42149
  have eq42547 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq332 y x
       have i₂ := eq42150
       grind)
    | exact superpose eq42150 eq332
    | (have j0 := eq332 y x
       grind)
    | exact resolve eq332 eq42150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332 eq42150
  have eq42563 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq42547
  have eq42564 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq42563
  have eq42574 : (σ x) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq94 y x
       have i₂ := eq42564
       grind)
    | exact superpose eq42564 eq94
    | (have j0 := eq94 y x
       grind)
    | exact resolve eq94 eq42564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq42564
  have eq42627 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) := by grind
  clear eq42574
  have eq48512 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq42627
       grind)
    | exact superpose eq42627 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq42627
       grind)
    | exact resolve eq13 eq42627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42627
  have eq48551 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq48512
  have eq48552 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq48551
  have eq48599 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq48552
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq48552
    | exact resolve eq48552 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48552
  have eq48600 : (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq48599
  have eq48618 : y = (τ (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq48600
       grind)
    | exact superpose eq48600 eq10
    | exact resolve eq10 eq48600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48600
  have eq48733 : x = y ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq48618
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq48618
    | exact resolve eq48618 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48618
  have eq48921 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq48733
       grind)
    | exact superpose eq48733 eq16
    | exact resolve eq16 eq48733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48733
  have eq48961 : (σ x) = (σ (k x y)) := by
    first
    | (have r₁ := eq48921
       have r₂ := eq22 x
       grind)
    | exact resolve eq48921 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48921
  have eq48991 : (k x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq48961
       grind)
    | exact superpose eq48961 eq10
    | exact resolve eq10 eq48961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48961
  have eq49107 : x = (k x y) := by
    first
    | (have i₁ := eq48991
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq48991
    | exact resolve eq48991 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48991
  have eq49487 : x = y ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq49107
       grind)
    | exact superpose eq49107 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq49107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49107
  have eq51622 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq49487
       grind)
    | exact superpose eq49487 eq16
    | exact resolve eq16 eq49487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49487
  have eq51676 : y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq51622
       have r₂ := eq22 x
       grind)
    | exact resolve eq51622 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51622
  have eq51686 : ∀ X0 : G, x = (M.op y x) ∨ (M.op X0 (M.op y (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq51676
       grind)
    | exact superpose eq51676 eq9
    | exact resolve eq9 eq51676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51676
  have eq52600 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op x x))) = X0 ∨ (M.op X1 (M.op y (M.op y y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq51686 X1
       grind)
    | exact superpose eq51686 eq9
    | (have j1 := eq51686 X1
       grind)
    | exact resolve eq9 eq51686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51686
  have eq63414 : ∀ X0 X1 : G, (M.op X0 (τ x)) = X0 ∨ (M.op X1 (M.op y (M.op y y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq307 x x X0
       have i₂ := eq52600 x X1
       grind)
    | exact superpose eq52600 eq307
    | (have j1 := eq52600 X0 X1
       grind)
    | exact resolve eq307 eq52600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307 eq52600
  have eq65347 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 ∨ (τ x) = (τ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq67 x
       have i₂ := eq63414 (τ x) X0
       grind)
    | exact superpose eq63414 eq67
    | (have j1 := eq63414 X0 X0
       grind)
    | exact resolve eq67 eq63414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63414
  have eq67331 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (τ x) = (τ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq65347 y
       grind)
    | exact superpose eq65347 eq9
    | exact resolve eq9 eq65347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67334 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (τ x) = (τ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq162 y y X0
       have i₂ := eq65347 y
       grind)
    | exact superpose eq65347 eq162
    | exact resolve eq162 eq65347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq65347
  have eq68525 : (σ (M.op x y)) ≠ (σ x) ∨ (τ x) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67334 (σ x)
       grind)
    | exact superpose eq67334 eq16
    | exact resolve eq16 eq67334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67334
  have eq71633 : (σ x) ≠ (σ x) ∨ (τ x) = (τ (M.op x x)) ∨ (τ x) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq68525
       have i₂ := eq67331 x
       grind)
    | exact superpose eq67331 eq68525
    | exact resolve eq68525 eq67331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67331 eq68525
  have eq71634 : (σ x) ≠ (σ x) ∨ (τ x) = (τ (M.op x x)) := by grind
  clear eq71633
  have eq71635 : (τ x) = (τ (M.op x x)) := by grind
  clear eq71634
  have eq71641 : ∀ X0 : G, (M.op X0 (σ (σ (M.op (M.op (τ x) (τ x)) (M.op (τ x) (τ x)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq258 x x
       have i₂ := eq71635
       grind)
    | exact superpose eq71635 eq258
    | exact resolve eq258 eq71635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq71642 : ∀ X0 : G, (M.op X0 (σ (M.op (M.op (τ x) (τ x)) (M.op (τ x) (τ x))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq260 x x
       have i₂ := eq71635
       grind)
    | exact superpose eq71635 eq260
    | exact resolve eq260 eq71635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq71661 : (M.op x x) = (σ (τ x)) := by
    first
    | (have i₁ := eq11 (M.op x x)
       have i₂ := eq71635
       grind)
    | exact superpose eq71635 eq11
    | exact resolve eq11 eq71635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71664 : (M.op (M.op x x) (M.op x x)) = (σ (M.op (τ x) (τ x))) := by
    first
    | (have i₁ := eq30 (M.op x x)
       have i₂ := eq71635
       grind)
    | exact superpose eq71635 eq30
    | exact resolve eq30 eq71635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71635
  have eq71925 : (M.op x x) = (M.op (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq71664
       have i₂ := eq30 x
       grind)
    | exact superpose eq30 eq71664
    | exact resolve eq71664 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71664
  have eq71928 : x = (M.op x x) := by
    first
    | (have i₁ := eq71661
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq71661
    | exact resolve eq71661 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71661
  have eq71947 : ∀ X0 : G, (M.op X0 (σ (M.op (τ (M.op x x)) (τ (M.op x x))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq71642 X0
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq71642
    | exact resolve eq71642 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71642
  have eq71948 : ∀ X0 : G, (M.op X0 (σ (σ (M.op (τ (M.op x x)) (τ (M.op x x)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq71641 X0
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq71641
    | exact resolve eq71641 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq71641
  have eq71973 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) (M.op x x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq71947 X0
       have i₂ := eq30 (M.op x x)
       grind)
    | exact superpose eq30 eq71947
    | exact resolve eq71947 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71947
  have eq71974 : ∀ X0 : G, (M.op X0 (σ (M.op (M.op x x) (M.op x x)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq71948 X0
       have i₂ := eq30 (M.op x x)
       grind)
    | exact superpose eq30 eq71948
    | exact resolve eq71948 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq71948
  have eq71999 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq71973 X0
       have i₂ := eq71925
       grind)
    | exact superpose eq71925 eq71973
    | exact resolve eq71973 eq71925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71973
  have eq72000 : ∀ X0 : G, (M.op X0 (σ (M.op x x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq71974 X0
       have i₂ := eq71925
       grind)
    | exact superpose eq71925 eq71974
    | exact resolve eq71974 eq71925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71925 eq71974
  have eq72024 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq71999 X0
       have i₂ := eq71928
       grind)
    | exact superpose eq71928 eq71999
    | exact resolve eq71999 eq71928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71999
  have eq72025 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq72000 X0
       have i₂ := eq71928
       grind)
    | exact superpose eq71928 eq72000
    | exact resolve eq72000 eq71928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71928 eq72000
  have eq72950 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq22504
       have i₂ := eq72024 y
       grind)
    | exact superpose eq72024 eq22504
    | exact resolve eq22504 eq72024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22504
  have eq72966 : (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq72950
       have i₂ := eq72025 (σ y)
       grind)
    | exact superpose eq72025 eq72950
    | exact resolve eq72950 eq72025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72950
  have eq72967 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq72966
  have eq77313 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq72967
       grind)
    | exact superpose eq72967 eq16
    | exact resolve eq16 eq72967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72967
  have eq77419 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq77313
       have r₂ := eq22 x
       grind)
    | exact resolve eq77313 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq77313
  have eq77420 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq77419
       grind)
    | exact superpose eq77419 eq16
    | exact resolve eq16 eq77419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77423 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq77419
       grind)
    | exact superpose eq77419 eq10
    | exact resolve eq10 eq77419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77419
  have eq77559 : x = y := by
    first
    | (have i₁ := eq77423
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq77423
    | exact resolve eq77423 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77423
  have eq77560 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq77420
       have i₂ := eq72025 (σ x)
       grind)
    | exact superpose eq72025 eq77420
    | exact resolve eq77420 eq72025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72025 eq77420
  have eq77561 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq77560
       have i₂ := eq77559
       grind)
    | exact superpose eq77559 eq77560
    | exact resolve eq77560 eq77559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77559 eq77560
  have eq77562 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq77561
       have i₂ := eq72024 x
       grind)
    | exact superpose eq72024 eq77561
    | exact resolve eq77561 eq72024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72024 eq77561
  have eq77563 : False := by grind
  exact eq77563

/-- `Equation443`: `x = x ◇ (y ◇ (y ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation443 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law443 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law443.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq48 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq94 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq320 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq94 x y
       grind)
    | exact superpose eq94 eq16
    | (have j1 := eq94 x y
       grind)
    | exact resolve eq16 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq1538 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq330 (τ X1) (τ X0)
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq330
    | (have j0 := eq330 (τ X1) (τ X0)
       grind)
    | exact resolve eq330 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq1545 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1538 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1538
    | (have j0 := eq1538 X0 X1
       grind)
    | exact resolve eq1538 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538
  have eq1548 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1545 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1545
    | (have j0 := eq1545 X0 X1
       grind)
    | exact resolve eq1545 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1545
  have eq1550 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1548 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1548
    | (have j0 := eq1548 X0 X1
       grind)
    | exact resolve eq1548 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548
  have eq1551 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1550 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1550
    | (have j0 := eq1550 X0 X1
       grind)
    | exact resolve eq1550 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550
  have eq1552 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1551 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1551
    | (have j0 := eq1551 X0 X1
       grind)
    | exact resolve eq1551 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551
  have eq1553 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1552 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1552
    | (have j0 := eq1552 X0 X1
       grind)
    | exact resolve eq1552 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552
  have eq1872 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq320
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq320
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq320
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq320
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq320 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq1873 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1872
  have eq22920 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1873
       grind)
    | exact superpose eq1873 eq16
    | exact resolve eq16 eq1873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1873
  have eq22921 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq22920
       have r₂ := eq22 x
       grind)
    | exact resolve eq22920 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22920
  have eq22923 : y ≠ y ∨ y = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq22921
       grind)
    | exact superpose eq22921 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq22921
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq22921
       grind)
    | exact resolve eq13 eq22921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22921
  have eq22958 : x = y ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22923
  have eq44217 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22958
       grind)
    | exact superpose eq22958 eq16
    | exact resolve eq16 eq22958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22958
  have eq44218 : y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq44217
       have r₂ := eq22 x
       grind)
    | exact resolve eq44217 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44217
  have eq44225 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq330 x y
       have i₂ := eq44218
       grind)
    | exact superpose eq44218 eq330
    | (have j0 := eq330 x y
       grind)
    | exact resolve eq330 eq44218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq44218
  have eq44243 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq44225
  have eq44244 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq44243
  have eq44370 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44244
       grind)
    | exact superpose eq44244 eq16
    | exact resolve eq16 eq44244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44372 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq44244
       grind)
    | exact superpose eq44244 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq44244
       grind)
    | exact resolve eq13 eq44244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44244
  have eq44413 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq44372
  have eq44414 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq44413
  have eq44456 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq44414
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq44414
    | exact resolve eq44414 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44414
  have eq44599 : y = (τ (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq44456
       grind)
    | exact superpose eq44456 eq10
    | exact resolve eq10 eq44456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44456
  have eq44710 : x = y ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq44599
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq44599
    | exact resolve eq44599 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44599
  have eq44712 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44710
       grind)
    | exact superpose eq44710 eq16
    | exact resolve eq16 eq44710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44710
  have eq44713 : (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq44712
       have r₂ := eq22 x
       grind)
    | exact resolve eq44712 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44712
  have eq44936 : (k y x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq44713
       grind)
    | exact superpose eq44713 eq10
    | exact resolve eq10 eq44713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44713
  have eq45048 : y = (k y x) := by
    first
    | (have i₁ := eq44936
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq44936
    | exact resolve eq44936 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44936
  have eq45060 : y ≠ y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1553 y x
       have i₂ := eq45048
       grind)
    | exact superpose eq45048 eq1553
    | (have j0 := eq1553 y x
       grind)
    | (have r₁ := eq1553 y x
       have r₂ := eq45048
       grind)
    | exact resolve eq1553 eq45048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553 eq45048
  have eq45075 : x = y ∨ y = (M.op x y) := by grind
  clear eq45060
  have eq45290 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq45075
       grind)
    | exact superpose eq45075 eq16
    | exact resolve eq16 eq45075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45075
  have eq45295 : y = (M.op x y) := by
    first
    | (have r₁ := eq45290
       have r₂ := eq22 x
       grind)
    | exact resolve eq45290 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45290
  have eq45300 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44370
       have i₂ := eq45295
       grind)
    | exact superpose eq45295 eq44370
    | exact resolve eq44370 eq45295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44370 eq45295
  have eq45344 : (σ x) = (σ y) := by grind
  clear eq45300
  have eq46265 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq45344
       grind)
    | exact superpose eq45344 eq10
    | exact resolve eq10 eq45344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45344
  have eq46377 : x = y := by
    first
    | (have i₁ := eq46265
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq46265
    | exact resolve eq46265 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46265
  have eq46381 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46377
       grind)
    | exact superpose eq46377 eq16
    | exact resolve eq16 eq46377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46377
  have eq46387 : False := by grind
  exact eq46387
