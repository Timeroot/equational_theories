import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_x_y_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
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
  have eq36 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
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
  have eq40 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq47 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq48 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq47 eq16
    | exact resolve eq16 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq64 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    grind
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq75
    | exact resolve eq75 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22 eq84
    | exact resolve eq84 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq90 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq38
    | (have j1 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq100 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq16
    | exact resolve eq16 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq91
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq16
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq101
  have eq116 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq39
    | (have j0 := eq39 (M.op x y)
       grind)
    | exact resolve eq39 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq154 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq116
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq116 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq116 eq16
    | exact resolve eq16 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq154
  have eq204 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq157
       have i₂ := eq11 sF1 sF1
       grind)
    | exact superpose eq11 eq157
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq157 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq206 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq204
  have eq208 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq48 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq48 eq14
    | exact resolve eq14 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq16
    | exact resolve eq16 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq348 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq16
    | exact resolve eq16 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq381 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq51 X0 X0
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 (M.op X1 X0)
       have i₂ := eq51 X1 X0
       grind)
    | exact superpose eq51 eq49
    | exact resolve eq49 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (M.op X1 X0)
       have i₂ := eq51 X1 X0
       grind)
    | exact superpose eq51 eq48
    | exact resolve eq48 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq51 X1 X0
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq422 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq50 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq50 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq51 X1 X0
       grind)
    | exact superpose eq51 eq50
    | exact resolve eq50 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq50 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq50 eq48
    | exact resolve eq48 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq51 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq50 X0 x x X3
       grind)
    | exact superpose eq50 eq51
    | exact resolve eq51 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq461 X0 X1
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq461
    | exact resolve eq461 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq534 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq66 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq536 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq534 X0
       have j1 := eq64 X0
       grind)
    | (have r₁ := eq534 X0
       have r₂ := eq64 X0
       grind)
    | exact resolve eq534 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq534
  have eq540 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X0 (M.op X1 X0)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq536 (M.op X1 X0)
       have i₂ := eq51 X1 X0
       grind)
    | exact superpose eq51 eq536
    | exact resolve eq536 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq246 X0 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq246
    | (have j0 := eq246 X0 y
       grind)
    | exact resolve eq246 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq22 eq246
    | (have j0 := eq246 X0 (M.op x y)
       grind)
    | exact resolve eq246 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq748 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (σ (k X0 X0))) (M.op (σ X0) (M.op X3 X3))) = X3 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 (σ X0) X1 X2 X3
       have i₂ := eq71 X0 X0
       grind)
    | exact superpose eq71 eq50
    | (have j1 := eq71 X0 X0
       grind)
    | exact resolve eq50 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq758 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq71 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq759 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq758 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq766 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (σ (k X0 X0))) (M.op (σ X0) (M.op X3 X3))) = X3 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq748 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq1141 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op y (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq208 eq209
    | exact resolve eq209 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq1562 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) = (M.op y (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq385 (M.op x sF0) (M.op x sF0)
       have i₂ := eq14 (M.op x sF0) sF0 x
       grind)
    | exact superpose eq14 eq385
    | exact resolve eq385 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq1571 : ∀ X0 : G, (M.op y (M.op X0 (M.op x y))) = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1562 X0
       have i₂ := eq51 X0 sF0
       grind)
    | exact superpose eq51 eq1562
    | exact resolve eq1562 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562
  have eq1769 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq422 X0 X0 X0
       grind)
    | exact superpose eq422 eq14
    | exact resolve eq14 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1772 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (M.op X0 (M.op X0 X0))
       have i₂ := eq422 X0 X0 X0
       grind)
    | exact superpose eq422 eq48
    | exact resolve eq48 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1773 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq49 (M.op X0 (M.op X0 X0))
       have i₂ := eq422 X0 X0 X0
       grind)
    | exact superpose eq422 eq49
    | exact resolve eq49 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1785 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    have f1785_12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
      intro X0 X1
      grind
    have f1785_13 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X1 (M.op X2 X2))) = X2 := by
      intro X0 X1 X2
      grind
    have f1785_22 : X0 ≠ (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) := by grind
    have f1785_68 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
      intro X0 X1
      first
      | (have i₁ := f1785_12 (M.op x (M.op x x)) X1
         have i₂ := f1785_13 x x x
         grind)
      | exact superpose f1785_13 f1785_12
      | exact resolve f1785_12 f1785_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1785_206 : X0 ≠ X0 := by
      first
      | (have i₁ := f1785_22
         have i₂ := f1785_68 X0 X1
         grind)
      | exact superpose f1785_68 f1785_22
      | (have r₁ := f1785_22
         have r₂ := f1785_68 X0 X1
         grind)
      | exact resolve f1785_22 f1785_68
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1785_208 : False := by grind
    exact f1785_208
  clear eq422
  have eq2014 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq381 X0
       have i₂ := eq1772 X0
       grind)
    | exact superpose eq1772 eq381
    | exact resolve eq381 eq1772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2043 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1772 eq384
    | exact resolve eq384 eq1772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1772
  have eq2054 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq384 eq2043
    | exact resolve eq2043 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2043
  have eq2087 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq48 eq2014
    | exact resolve eq2014 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq2014
  have eq2238 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1773 eq384
    | exact resolve eq384 eq1773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1773
  have eq2249 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq384 eq2238
    | exact resolve eq2238 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384 eq2238
  have eq4422 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq759 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq759
    | (have j0 := eq759 X0
       have j1 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq759 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq4430 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4422 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4422
  have eq4916 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op y (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq387 X1 X0 X1 X0
       have i₂ := eq470 X0 X1
       grind)
    | exact superpose eq470 eq387
    | exact resolve eq387 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq7572 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq93 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq93
    | (have j0 := eq93 y
       grind)
    | exact resolve eq93 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq7595 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq7572
  have eq7600 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq7595
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq7595
    | exact resolve eq7595 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq7595
  have eq7870 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq117
    | (have j0 := eq117 (M.op x y)
       grind)
    | exact resolve eq117 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq7892 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq7870
  have eq7896 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq116 eq7892
    | exact resolve eq7892 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq7892
  have eq12505 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq387 (σ X0) (σ X0) (σ (k X0 X0)) (M.op x x)
       have i₂ := eq766 X0 x x (σ X0)
       grind)
    | exact superpose eq766 eq387
    | (have j1 := eq766 X0 x x x
       grind)
    | exact resolve eq387 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387 eq766
  have eq19335 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq208 eq162
    | exact resolve eq162 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq19336 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq208 eq19335
    | exact resolve eq19335 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq19335
  have eq21989 : ∀ X0 X1 : G, (M.op y (M.op x y)) = (M.op (M.op (M.op X0 X1) (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq1141 eq447
    | exact resolve eq447 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq22061 : ∀ X0 X1 : G, (M.op y (M.op x y)) = (M.op (M.op (M.op X0 X1) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq21989 X0 X1
       have i₂ := eq51 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq51 eq21989
    | exact resolve eq21989 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21989
  have eq22094 : ∀ X0 X1 : G, (M.op y (M.op x y)) = (M.op (M.op (M.op X0 X1) (M.op x y)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq22061 X0 X1
       have i₂ := eq1785 sF0 sF0
       grind)
    | exact superpose eq1785 eq22061
    | exact resolve eq22061 eq1785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22061
  have eq22139 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq22094 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq381 X0
       grind)
    | exact superpose eq381 eq22094
    | exact resolve eq22094 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22094
  have eq24142 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq447 X0 (M.op X1 X0) X2 X3 X4
       have i₂ := eq1769 X0 X0 X1
       grind)
    | exact superpose eq1769 eq447
    | exact resolve eq447 eq1769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24209 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq381 X2
       have i₂ := eq1769 X2 X0 X1
       grind)
    | exact superpose eq1769 eq381
    | exact resolve eq381 eq1769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1769
  have eq24335 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24142 X0 X1 x x x
       have i₂ := eq447 X0 X0 x x x
       grind)
    | exact superpose eq447 eq24142
    | exact resolve eq24142 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447 eq24142
  have eq25773 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq4916 (M.op x sF0) y
       have i₂ := eq24209 sF0 x y
       grind)
    | exact superpose eq24209 eq4916
    | exact resolve eq4916 eq24209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4916 eq24209
  have eq33198 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq85 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33199 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq33198
    | exact resolve eq33198 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33198
  have eq33210 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq33199
       have r₂ := eq29
       grind)
    | exact resolve eq33199 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33199
  have eq33215 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq33210
  have eq33361 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq33215 eq85
    | exact resolve eq85 eq33215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq33215
  have eq33372 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq33361
  have eq33392 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  have eq33413 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq33372 eq536
    | exact resolve eq536 eq33372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33484 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq33372 eq24335
    | exact resolve eq24335 eq33372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33372
  have eq33486 : y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq28 eq33484
    | exact resolve eq33484 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33484
  have eq33519 : x = (M.op x (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq381 x
       have i₂ := eq33486
       grind)
    | exact superpose eq33486 eq381
    | exact resolve eq381 eq33486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33554 : (M.op x y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq51 x x
       have i₂ := eq33486
       grind)
    | exact superpose eq33486 eq51
    | exact resolve eq51 eq33486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33577 : x = (M.op y (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1785 x x
       have i₂ := eq33486
       grind)
    | exact superpose eq33486 eq1785
    | exact resolve eq1785 eq33486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33486
  have eq33608 : x = (M.op y (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq33577
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq33577
    | exact resolve eq33577 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33577
  have eq33620 : (M.op x y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq33554
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq33554
    | exact resolve eq33554 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33554
  have eq33634 : x = (M.op y y) ∨ x = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq33519
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq33519
    | exact resolve eq33519 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33519
  have eq34072 : x ≠ (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq33620
  have eq34866 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq24335 y y
       have i₂ := eq33634
       grind)
    | exact superpose eq33634 eq24335
    | exact resolve eq24335 eq33634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33634
  have eq34869 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq34866
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq34866
    | exact resolve eq34866 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34866
  have eq34893 : (M.op y x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq34869 eq1571
    | exact resolve eq1571 eq34869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34898 : (M.op x (M.op x y)) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq34869 eq22139
    | exact resolve eq22139 eq34869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34899 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq34869 eq25773
    | exact resolve eq25773 eq34869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34902 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq34869 eq51
    | exact resolve eq51 eq34869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34963 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq34899
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq34899
    | exact resolve eq34899 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34899
  have eq34990 : y = (M.op y (M.op y (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq381 y
       have i₂ := eq34963
       grind)
    | exact superpose eq34963 eq381
    | exact resolve eq381 eq34963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36202 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq34902 eq34893
    | exact resolve eq34893 eq34902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34893 eq34902
  have eq36259 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq36202
  have eq36345 : y = (M.op y (M.op x (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq34898 eq34990
    | exact resolve eq34990 eq34898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34898 eq34990
  have eq36410 : y = (M.op y (M.op x (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq36345
  have eq36660 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq34869 eq36410
    | exact resolve eq36410 eq34869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34869 eq36410
  have eq36713 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq36660
  have eq36744 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq36259
       have i₂ := eq36713
       grind)
    | exact superpose eq36713 eq36259
    | exact resolve eq36259 eq36713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36259 eq36713
  have eq36794 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq36744
  have eq37657 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1785 x x
       have i₂ := eq36794
       grind)
    | exact superpose eq36794 eq1785
    | exact resolve eq1785 eq36794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36794
  have eq37687 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq37657
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq37657
    | exact resolve eq37657 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37657
  have eq38923 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq37687 eq19336
    | exact resolve eq19336 eq37687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37687
  have eq38987 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq38923
  have eq39009 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq38987
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38987
    | exact resolve eq38987 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38987
  have eq39047 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq7896 eq39009
    | exact resolve eq39009 eq7896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7896 eq39009
  have eq41261 : (τ (σ y)) = (k y x) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq33392 eq100
    | exact resolve eq100 eq33392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq33392
  have eq41284 : y = (k y x) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq31 eq41261
    | exact resolve eq41261 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41261
  have eq41296 : (τ (σ y)) = (k x y) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq33413 eq59
    | exact resolve eq59 eq33413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33413
  have eq41324 : y = (k x y) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq31 eq41296
    | exact resolve eq41296 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41296
  have eq51744 : y = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq41284
       grind)
    | exact superpose eq41284 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq41284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41284
  have eq51745 : y = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq51744
  have eq52533 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq41324
       grind)
    | exact superpose eq41324 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq41324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41324
  have eq52534 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq52533
  have eq52544 : y = (M.op x x) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq52534
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq52534
    | exact resolve eq52534 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52534
  have eq52586 : x = (M.op x (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq381 x
       have i₂ := eq52544
       grind)
    | exact superpose eq52544 eq381
    | exact resolve eq381 eq52544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52544
  have eq52738 : x = (M.op y y) ∨ x = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq52586
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq52586
    | exact resolve eq52586 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52586
  have eq56405 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq24335 y y
       have i₂ := eq52738
       grind)
    | exact superpose eq52738 eq24335
    | exact resolve eq24335 eq52738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52738
  have eq56420 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq56405
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq56405
    | exact resolve eq56405 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56405
  have eq56469 : (M.op y x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq56420 eq1571
    | exact resolve eq1571 eq56420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1571
  have eq56476 : (M.op x (M.op x y)) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq56420 eq22139
    | exact resolve eq22139 eq56420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22139
  have eq56477 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq56420 eq25773
    | exact resolve eq25773 eq56420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25773
  have eq56480 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq56420 eq51
    | exact resolve eq51 eq56420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56563 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq56477
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq56477
    | exact resolve eq56477 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56477
  have eq56585 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq107
       have i₂ := eq56563
       grind)
    | exact superpose eq56563 eq107
    | exact resolve eq107 eq56563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56619 : y = (M.op y (M.op y (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq381 y
       have i₂ := eq56563
       grind)
    | exact superpose eq56563 eq381
    | exact resolve eq381 eq56563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381 eq56563
  have eq56734 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq56585
  have eq56777 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq22 eq56734
    | exact resolve eq56734 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56734
  have eq56860 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq7600 eq56777
    | exact resolve eq56777 eq7600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7600
  have eq59634 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq56480 eq56469
    | exact resolve eq56469 eq56480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56469 eq56480
  have eq59708 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq59634
  have eq59953 : y = (M.op y (M.op x (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq56476 eq56619
    | exact resolve eq56619 eq56476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56476 eq56619
  have eq60029 : y = (M.op y (M.op x (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq59953
  have eq60366 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq56420 eq60029
    | exact resolve eq60029 eq56420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56420 eq60029
  have eq60435 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq60366
  have eq60498 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq59708
       have i₂ := eq60435
       grind)
    | exact superpose eq60435 eq59708
    | exact resolve eq59708 eq60435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59708 eq60435
  have eq60566 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq60498
  have eq60788 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1785 x x
       have i₂ := eq60566
       grind)
    | exact superpose eq60566 eq1785
    | exact resolve eq1785 eq60566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1785 eq60566
  have eq60831 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq60788
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq60788
    | exact resolve eq60788 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60788
  have eq61029 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq60831 eq19336
    | exact resolve eq19336 eq60831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19336 eq60831
  have eq61115 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq61029
  have eq61147 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq61115
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq61115
    | exact resolve eq61115 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61115
  have eq76388 : (M.op x y) = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq51 y x
       have i₂ := eq51745
       grind)
    | exact superpose eq51745 eq51
    | exact resolve eq51 eq51745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq76406 : y = (k (M.op x y) y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq540 x y
       have i₂ := eq51745
       grind)
    | exact superpose eq51745 eq540
    | exact resolve eq540 eq51745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540 eq51745
  have eq76514 : y = (k (M.op x y) y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq76406
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq76406
    | exact resolve eq76406 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76406
  have eq76527 : (M.op x y) = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq76388
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq76388
    | exact resolve eq76388 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76388
  have eq94506 : x ≠ (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq76527
  have eq753714 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  have eq754097 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq56860
  have eq778855 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq753714 eq56777
    | exact resolve eq56777 eq753714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56777 eq753714
  have eq778992 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq778855
  have eq779037 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq778992
       have r₂ := eq754097
       grind)
    | exact resolve eq778992 eq754097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754097 eq778992
  have eq779095 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq779037 eq465
    | exact resolve eq465 eq779037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq1005215 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq39047 eq779095
    | exact resolve eq779095 eq39047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39047 eq779095
  have eq1005683 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq1005215
  have eq1005755 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq28 eq1005683
    | exact resolve eq1005683 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005683
  have eq1005772 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1005755
       have r₂ := eq29
       grind)
    | exact resolve eq1005755 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005755
  have eq1006997 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1005772
  have eq1007559 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1006997 eq61147
    | exact resolve eq61147 eq1006997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61147 eq1006997
  have eq1007703 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1007559
  have eq1007809 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1007703 eq2249
    | exact resolve eq2249 eq1007703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007703
  have eq1008009 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq28 eq1007809
    | exact resolve eq1007809 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007809
  have eq1010156 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1008009 eq779037
    | exact resolve eq779037 eq1008009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779037 eq1008009
  have eq1010635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq1010156
  have eq1010740 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1010635
       have r₂ := eq29
       grind)
    | exact resolve eq1010635 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010635
  have eq1010798 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1010740 eq30
    | exact resolve eq30 eq1010740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010740
  have eq1010977 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq1010798
    | exact resolve eq1010798 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010798
  have eq1010978 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1010977
  have eq1010979 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1010978 eq22
    | exact resolve eq22 eq1010978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1011046 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1010978 eq573
    | exact resolve eq573 eq1010978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq1011342 : x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1010978 eq33608
    | exact resolve eq33608 eq1010978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33608
  have eq1011689 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq1010978
  have eq1011692 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1011342
  have eq1011828 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1011692
       have r₂ := eq34072
       grind)
    | exact resolve eq1011692 eq34072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34072 eq1011692
  have eq1011921 : ∀ X0 : G, (τ (k X0 (σ y))) = (τ (k X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1011046 X0
       have i₂ := eq572 X0
       grind)
    | exact superpose eq572 eq1011046
    | exact resolve eq1011046 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq1011046
  have eq1011976 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1010979
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq1010979
    | exact resolve eq1010979 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010979
  have eq1012891 : (k x y) = (τ (k (σ x) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1011976 eq59
    | exact resolve eq59 eq1011976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq1012987 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1011976 eq2249
    | exact resolve eq2249 eq1011976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1013576 : (k x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq63 eq1012891
    | exact resolve eq1012891 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012891
  have eq1076434 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq34963
       have i₂ := eq1011828
       grind)
    | exact superpose eq1011828 eq34963
    | exact resolve eq34963 eq1011828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34963 eq1011828
  have eq1077165 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1076434
  have eq1077430 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1077165 eq2249
    | exact resolve eq2249 eq1077165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2249
  have eq1077550 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1077165 eq1012987
    | exact resolve eq1012987 eq1077165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012987
  have eq1077553 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1077550
  have eq1077637 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq28 eq1077430
    | exact resolve eq1077430 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077430
  have eq1083295 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1011976 eq1077637
    | exact resolve eq1077637 eq1011976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1083344 : (σ y) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1077637 eq536
    | exact resolve eq536 eq1077637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077637
  have eq1083838 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1083295
  have eq1084501 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1011976 eq1083344
    | exact resolve eq1083344 eq1011976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011976 eq1083344
  have eq1084514 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1084501
  have eq1084624 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1083838 eq2087
    | exact resolve eq2087 eq1083838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2087 eq1083838
  have eq1086511 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1077165 eq1084514
    | exact resolve eq1084514 eq1077165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084514
  have eq1086526 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1086511
  have eq1089008 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1077165 eq1084624
    | exact resolve eq1084624 eq1077165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077165 eq1084624
  have eq1089354 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1089008
  have eq1093161 : (τ (σ (M.op x y))) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1086526 eq63
    | exact resolve eq63 eq1086526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1086526
  have eq1093198 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq32 eq1093161
    | exact resolve eq1093161 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093161
  have eq1098121 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1093198 eq1013576
    | exact resolve eq1013576 eq1093198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013576 eq1093198
  have eq1098149 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1098121
  have eq1104590 : ∀ X0 : G, (k X0 (τ (σ y))) = (τ (k (σ X0) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1011921 eq348
    | exact resolve eq348 eq1011921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011921
  have eq1105382 : ∀ X0 : G, (k X0 (τ (σ (M.op x y)))) = (k X0 (τ (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1104590 X0
       have i₂ := eq348 X0 sF1
       grind)
    | exact superpose eq348 eq1104590
    | exact resolve eq1104590 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348 eq1104590
  have eq1105434 : ∀ X0 : G, (k X0 y) = (k X0 (τ (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq31 eq1105382
    | exact resolve eq1105382 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105382
  have eq1105450 : ∀ X0 : G, (k X0 y) = (k X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq32 eq1105434
    | exact resolve eq1105434 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105434
  have eq1308333 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1077553 eq1089354
    | exact resolve eq1089354 eq1077553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077553 eq1089354
  have eq1308652 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1308333
  have eq1310729 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1308652 eq206
    | exact resolve eq206 eq1308652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq1308652
  have eq1311335 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1310729
  have eq1311399 : x = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq1311335
    | exact resolve eq1311335 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311335
  have eq1311478 : x = (k (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1311399 eq1105450
    | exact resolve eq1105450 eq1311399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105450 eq1311399
  have eq1311658 : x = (k (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1311478
  have eq1314792 : x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq76514 eq1311658
    | exact resolve eq1311658 eq76514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76514 eq1311658
  have eq1314972 : x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq1314792
  have eq1315045 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1314972
       have r₂ := eq1011689
       grind)
    | exact resolve eq1314972 eq1011689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011689 eq1314972
  have eq1315093 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1315045
       have r₂ := eq94506
       grind)
    | exact resolve eq1315045 eq94506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94506 eq1315045
  have eq1459229 : x = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by grind
  clear eq1315093
  have eq1462985 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1098149
       have i₂ := eq1459229
       grind)
    | exact superpose eq1459229 eq1098149
    | exact resolve eq1098149 eq1459229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098149 eq1459229
  have eq1463043 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1462985
  have eq1463946 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24335 y y
       have i₂ := eq1463043
       grind)
    | exact superpose eq1463043 eq24335
    | exact resolve eq24335 eq1463043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463043
  have eq1464189 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1463946
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq1463946
    | exact resolve eq1463946 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463946
  have eq1464190 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1464189
  have eq1464398 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1464190 eq30
    | exact resolve eq30 eq1464190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1464190
  have eq1464606 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq1464398
    | exact resolve eq1464398 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1464398
  have eq1464607 : x = (M.op x y) := by grind
  clear eq1464606
  have eq1464609 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1464607 eq22
    | exact resolve eq22 eq1464607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1464720 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq1464607 eq2054
    | exact resolve eq2054 eq1464607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2054
  have eq1465578 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1464720
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq1464720
    | exact resolve eq1464720 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1464720
  have eq1465648 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1464609
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1464609
    | exact resolve eq1464609 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1464609
  have eq1465654 : x = (M.op y y) := by
    first
    | exact superpose eq1464607 eq1465578
    | exact resolve eq1465578 eq1464607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465578
  have eq1465661 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1465648 eq28
    | exact resolve eq28 eq1465648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1465899 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq107
       have i₂ := eq1465654
       grind)
    | exact superpose eq1465654 eq107
    | exact resolve eq107 eq1465654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq1466040 : y = (k y x) := by grind
  have eq1466061 : y = (k x y) := by
    first
    | (have i₁ := eq536 y
       have i₂ := eq1465654
       grind)
    | exact superpose eq1465654 eq536
    | exact resolve eq536 eq1465654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1466099 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq4430 y
       have i₂ := eq1465654
       grind)
    | exact superpose eq1465654 eq4430
    | (have j0 := eq4430 y
       grind)
    | exact resolve eq4430 eq1465654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4430 eq1465654
  have eq1466936 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1466099
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq1466099
    | exact resolve eq1466099 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466099
  have eq1466976 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1465899
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1465899
    | exact resolve eq1465899 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465899
  have eq1467087 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1466936
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1466936
    | exact resolve eq1466936 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466936
  have eq1467100 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1465648 eq1466976
    | exact resolve eq1466976 eq1465648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466976
  have eq1467145 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1465648 eq1467087
    | exact resolve eq1467087 eq1465648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467087
  have eq1467159 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1467145
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq1467145
    | exact resolve eq1467145 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467145
  have eq1467800 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq90
       have i₂ := eq1466040
       grind)
    | exact superpose eq1466040 eq90
    | exact resolve eq90 eq1466040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq1466040
  have eq1467961 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1465648 eq1467800
    | exact resolve eq1467800 eq1465648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467800
  have eq1468023 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1467961
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq1467961
    | exact resolve eq1467961 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467961
  have eq1468334 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq46
       have i₂ := eq1466061
       grind)
    | exact superpose eq1466061 eq46
    | exact resolve eq46 eq1466061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq1466061
  have eq1468473 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1465648 eq1468334
    | exact resolve eq1468334 eq1465648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468334
  have eq1468507 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq1468473
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq1468473
    | exact resolve eq1468473 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468473
  have eq1468731 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1468507 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq11 eq1468507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468507
  have eq1468761 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1465661 eq1468731
    | exact resolve eq1468731 eq1465661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468731
  have eq1500362 : (τ (σ (M.op x y))) = (k y y) ∨ x = y := by
    first
    | exact superpose eq1467100 eq106
    | exact resolve eq106 eq1467100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq1500698 : (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq32 eq1500362
    | exact resolve eq1500362 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1500362
  have eq1500729 : x = (k y y) ∨ x = y := by
    first
    | exact superpose eq1464607 eq1500698
    | exact resolve eq1500698 eq1464607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1500698
  have eq1500958 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq12505 y
       have i₂ := eq1500729
       grind)
    | exact superpose eq1500729 eq12505
    | (have j0 := eq12505 y
       grind)
    | exact resolve eq12505 eq1500729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12505 eq1500729
  have eq1501097 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1500958
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq1500958
    | exact resolve eq1500958 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1500958
  have eq1501295 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1501097
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1501097
    | exact resolve eq1501097 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501097
  have eq1501492 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28 eq1501295
    | exact resolve eq1501295 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1501295
  have eq1501679 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1501492
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq1501492
    | exact resolve eq1501492 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501492
  have eq3589678 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1468761 eq536
    | exact resolve eq536 eq1468761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq3591016 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1468023 eq3589678
    | exact resolve eq3589678 eq1468023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468023 eq3589678
  have eq3592680 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3591016 eq24335
    | exact resolve eq24335 eq3591016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24335 eq3591016
  have eq3593012 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1465661 eq3592680
    | exact resolve eq3592680 eq1465661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3592680
  have eq3593498 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq3593012
       have r₂ := eq29
       grind)
    | exact resolve eq3593012 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3593012
  have eq3696237 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq1501679
  have eq3697615 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3593498 eq3696237
    | (have r₁ := eq3696237
       have r₂ := eq3593498
       grind)
    | exact resolve eq3696237 eq3593498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3593498 eq3696237
  have eq3697618 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq3697615
  have eq3697619 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq3697618
       have r₂ := eq1467159
       grind)
    | exact resolve eq3697618 eq1467159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467159 eq3697618
  have eq3697704 : (σ y) = (k (σ y) (σ y)) ∨ x = y := by grind
  clear eq3697619
  have eq3699885 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq3697704 eq1467100
    | exact resolve eq1467100 eq3697704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467100 eq3697704
  have eq3700220 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq3699885
  have eq3700477 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq3700220 eq31
    | exact resolve eq31 eq3700220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3700220
  have eq3701484 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32 eq3700477
    | exact resolve eq3700477 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq3700477
  have eq3701603 : x = y ∨ x = y := by
    first
    | exact superpose eq1464607 eq3701484
    | exact resolve eq3701484 eq1464607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1464607 eq3701484
  have eq3701604 : x = y := by grind
  clear eq3701603
  have eq3701691 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq3701604
       grind)
    | exact superpose eq3701604 eq26
    | exact resolve eq26 eq3701604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3701604
  have eq3703620 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3701691
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3701691
    | exact resolve eq3701691 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3701691
  have eq3703911 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1465648 eq3703620
    | exact resolve eq3703620 eq1465648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465648 eq3703620
  have eq3704723 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3703911 eq1465661
    | exact resolve eq1465661 eq3703911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465661
  have eq3710963 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3704723 eq1468761
    | exact resolve eq1468761 eq3704723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468761
  have eq3711795 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq3710963
  have eq3712439 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3703911 eq3711795
    | exact resolve eq3711795 eq3703911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3711795
  have eq3712935 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq3712439
       have r₂ := eq29
       grind)
    | exact resolve eq3712439 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3712439
  have eq3713231 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3703911 eq3712935
    | exact resolve eq3712935 eq3703911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3703911 eq3712935
  have eq3713436 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3704723 eq3713231
    | exact resolve eq3713231 eq3704723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3704723 eq3713231
  have eq3713559 : False := by grind
  exact eq3713559

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_pyy_pyx_pyx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X2 X2))) = X2 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 X0
       have i₂ := eq11 X1 X0
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
  have eq104 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq111 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | (have i₁ := eq104 X1 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq104
    | (have j0 := eq104 X0 X0
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq104 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq104 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | exact resolve eq104 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq104 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq116 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq111 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq118 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq114 (σ X0)
       grind)
    | exact superpose eq114 eq10
    | exact resolve eq10 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq118 X0
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq118
    | exact resolve eq118 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq267 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq51 (M.op sF4 sF4)
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq114 (τ X0)
       grind)
    | exact superpose eq114 eq34
    | exact resolve eq34 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq342 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq342
    | exact resolve eq342 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq356 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq352 X0
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq352
    | exact resolve eq352 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq352
  have eq602 : ∀ X0 : G, (σ X0) = (M.op y (M.op (M.op x y) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq50 (σ X0)
       have i₂ := eq127 X0
       grind)
    | exact superpose eq127 eq50
    | exact resolve eq50 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq633 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq641 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq52 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq725 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq740 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq53 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq52 X0 x x X3
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq746 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq747 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq754 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq747 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq747
    | exact resolve eq747 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq755 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq746 X0 X1 X2 X3
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq746
    | exact resolve eq746 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq926 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq356 X0
       grind)
    | exact superpose eq356 eq16
    | exact resolve eq16 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq1091 : ∀ X0 : G, (τ X0) = (M.op y (M.op (M.op x y) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq50 (τ X0)
       have i₂ := eq926 X0
       grind)
    | exact superpose eq926 eq50
    | exact resolve eq50 eq926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926
  have eq1376 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq40 eq116
    | (have j0 := eq116 (σ y) (σ X0)
       grind)
    | exact resolve eq116 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1377 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (M.op X1 X1) = (k (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X1
       have i₂ := eq116 X1 (τ X0)
       grind)
    | exact superpose eq116 eq34
    | (have j1 := eq116 X1 (τ X0)
       grind)
    | exact resolve eq34 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq1397 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq116 y x
       grind)
    | exact superpose eq116 eq44
    | (have j1 := eq116 y x
       grind)
    | exact resolve eq44 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq1425 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq1397
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1397
    | exact resolve eq1397 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397
  have eq1454 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq1425
    | exact resolve eq1425 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425
  have eq1466 : (k x y) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1454
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1454
    | exact resolve eq1454 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454
  have eq1540 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X3) (M.op X0 (M.op X1 X0)))) ∨ (M.op X2 X3) = X2 ∨ (M.op X2 X3) = (k X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq80 X3 X2 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq80
    | (have j0 := eq80 X3 X2 X2
       grind)
    | exact resolve eq80 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq2844 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq273 eq50
    | exact resolve eq50 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2845 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq273 eq51
    | exact resolve eq51 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq2907 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq267 eq2845
    | exact resolve eq2845 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2845
  have eq2908 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq267 eq2844
    | exact resolve eq2844 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2844
  have eq3299 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2907 eq2908
    | exact resolve eq2908 eq2907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2908
  have eq3578 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq694 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq694 X0 X0 X0
       grind)
    | exact superpose eq694 eq694
    | exact resolve eq694 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3620 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq694 X0 X0 X0
       grind)
    | exact superpose eq694 eq14
    | exact resolve eq14 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3621 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq694 X0 X0 X0
       grind)
    | exact superpose eq694 eq50
    | exact resolve eq50 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3622 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq694 X0 X0 X0
       grind)
    | exact superpose eq694 eq51
    | exact resolve eq51 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq3642 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq740 (M.op x (M.op x x)) x
       have i₂ := eq694 x x x
       grind)
    | exact superpose eq694 eq740
    | exact resolve eq740 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq3821 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq633 X0
       have i₂ := eq3621 X0
       grind)
    | exact superpose eq3621 eq633
    | exact resolve eq633 eq3621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3937 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq602 eq3821
    | exact resolve eq3821 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq3939 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | exact superpose eq1091 eq3821
    | exact resolve eq3821 eq1091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq4140 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq633 X0
       have i₂ := eq3622 X0
       grind)
    | exact superpose eq3622 eq633
    | exact resolve eq633 eq3622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3622
  have eq4567 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq26 eq3642
    | (have j0 := eq3642 (σ y) (σ x)
       grind)
    | exact resolve eq3642 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3642
  have eq4658 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) := by
    first
    | (have i₁ := eq4567
       have i₂ := eq3621 sF3
       grind)
    | exact superpose eq3621 eq4567
    | exact resolve eq4567 eq3621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4567
  have eq9766 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq755 X0 X1 X2 X3
       have i₂ := eq754 X0 X1
       grind)
    | exact superpose eq754 eq755
    | exact resolve eq755 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq9962 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op y (M.op (M.op x y) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9766 X1 (M.op X0 X0) (M.op X1 X1) x
       have i₂ := eq694 x X1 X0
       grind)
    | exact superpose eq694 eq9766
    | exact resolve eq9766 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq9989 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op X2 X1)) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9766 (M.op X3 (M.op X2 X1)) (M.op X0 X0) X1 X2
       have i₂ := eq14 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq14 eq9766
    | exact resolve eq9766 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10068 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X2 (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X1 X2)) X2 X1
       have i₂ := eq9766 X0 (M.op X1 X2) (M.op X1 X2) X0
       grind)
    | exact superpose eq9766 eq14
    | exact resolve eq14 eq9766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9766
  have eq17037 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (k x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1376 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1376
    | (have j0 := eq1376 x
       grind)
    | exact resolve eq1376 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376
  have eq17097 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (k x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq17037
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq17037
    | exact resolve eq17037 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17037
  have eq17121 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (k x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq17097
    | exact resolve eq17097 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17097
  have eq17142 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (k x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq17121
    | exact resolve eq17121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17121
  have eq17151 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq17142
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq17142
    | exact resolve eq17142 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq17142
  have eq18446 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (M.op x X0)) ∨ x = (M.op x X0) ∨ (M.op X0 X0) = (k x X0) := by
    intro X0
    first
    | exact superpose eq28 eq1377
    | exact resolve eq1377 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377
  have eq18528 : ∀ X0 : G, (σ (k x X0)) = (σ (M.op x X0)) ∨ x = (M.op x X0) ∨ (M.op X0 X0) = (k x X0) := by
    intro X0
    first
    | exact superpose eq35 eq18446
    | (have j0 := eq18446 X0
       grind)
    | exact resolve eq18446 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq18446
  have eq24658 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op y (M.op (M.op x y) (M.op X0 X0)))) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1540 X0 X0 X1 X0
       have i₂ := eq754 X0 X0
       grind)
    | exact superpose eq754 eq1540
    | (have j0 := eq1540 X0 X1 X1 X0
       grind)
    | exact resolve eq1540 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754 eq1540
  have eq24950 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | exact superpose eq50 eq24658
    | (have j0 := eq24658 X0 X1
       grind)
    | exact resolve eq24658 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq24658
  have eq64690 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq633 X2
       have i₂ := eq3620 X2 X0 X1
       grind)
    | exact superpose eq3620 eq633
    | exact resolve eq633 eq3620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq64913 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq725 X0 (M.op X1 X0) X2 X3 X4
       have i₂ := eq3620 X0 X0 X1
       grind)
    | exact superpose eq3620 eq725
    | exact resolve eq725 eq3620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3620
  have eq65134 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq64913 X0 X1 x x x
       have i₂ := eq725 X0 X0 x x x
       grind)
    | exact superpose eq725 eq64913
    | exact resolve eq64913 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725 eq64913
  have eq66941 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4140 (M.op (M.op x sF4) sF3)
       have i₂ := eq64690 sF4 x sF3
       grind)
    | exact superpose eq64690 eq4140
    | exact resolve eq4140 eq64690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4140
  have eq66958 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq66941 X0
       have i₂ := eq65134 sF3 (M.op X0 sF4)
       grind)
    | exact superpose eq65134 eq66941
    | exact resolve eq66941 eq65134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65134 eq66941
  have eq129368 : ∀ X0 : G, (M.op y (M.op y y)) = (M.op (M.op X0 (M.op x x)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq3578 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3578
    | (have j0 := eq3578 y X0 x
       grind)
    | exact resolve eq3578 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129403 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq3578
    | (have j0 := eq3578 (σ y) X0 (σ x)
       grind)
    | exact resolve eq3578 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130776 : ∀ X0 : G, (M.op y (M.op (M.op x y) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq129403 X0
       have i₂ := eq3621 sF3
       grind)
    | exact superpose eq3621 eq129403
    | exact resolve eq129403 eq3621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129403
  have eq153960 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  have eq158377 : (M.op x y) = (M.op (M.op x y) (M.op (M.op x x) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq129368 eq64690
    | exact resolve eq64690 eq129368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64690 eq129368
  have eq225081 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op X0 (M.op X0 X0))) (M.op X2 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9989 X2 (M.op X1 X0) (M.op x (M.op X1 X1)) X3
       have i₂ := eq3578 X0 x X1
       grind)
    | exact superpose eq3578 eq9989
    | exact resolve eq9989 eq3578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3578
  have eq225260 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op y (M.op (M.op x y) (M.op (M.op X2 (M.op X0 (M.op X0 X0))) (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3621 eq9989
    | exact resolve eq9989 eq3621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3621
  have eq226234 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq9989 eq225260
    | exact resolve eq225260 eq9989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225260
  have eq226273 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq9989 eq225081
    | exact resolve eq225081 eq9989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9989 eq225081
  have eq240854 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq226273 X1 X0 X2
       have i₂ := eq226273 X1 X3 X2
       grind)
    | (have i₁ := eq226273 X0 X1 X2
       have i₂ := eq226273 X0 X0 X2
       grind)
    | exact superpose eq226273 eq226273
    | exact resolve eq226273 eq226273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226273
  have eq248243 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq9962 eq10068
    | exact resolve eq10068 eq9962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9962 eq10068
  have eq309004 : (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq130776 eq248243
    | exact resolve eq248243 eq130776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130776
  have eq310161 : (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (M.op x y) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq309004
       have i₂ := eq226234 sF2 (M.op sF4 sF4)
       grind)
    | exact superpose eq226234 eq309004
    | exact resolve eq309004 eq226234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226234 eq309004
  have eq310634 : (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq267 eq310161
    | exact resolve eq310161 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267 eq310161
  have eq310874 : (σ y) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq4658 eq310634
    | exact resolve eq310634 eq4658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4658 eq310634
  have eq311695 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq310874
       have i₂ := eq240854 sF0 sF2 (M.op sF3 sF4) x
       grind)
    | (have i₁ := eq310874
       have i₂ := eq240854 X0 sF2 (M.op sF3 sF4) sF0
       grind)
    | exact superpose eq240854 eq310874
    | exact resolve eq310874 eq240854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240854 eq310874
  have eq313964 : (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (σ x) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq311695 eq248243
    | exact resolve eq248243 eq311695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248243 eq311695
  have eq314331 : (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq313964
       have i₂ := eq53 sF3 sF4
       grind)
    | exact superpose eq53 eq313964
    | exact resolve eq313964 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq313964
  have eq314447 : (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq2907 eq314331
    | exact resolve eq314331 eq2907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2907 eq314331
  have eq314505 : (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq3299 eq314447
    | exact resolve eq314447 eq3299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3299 eq314447
  have eq314533 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq66958 eq314505
    | exact resolve eq314505 eq66958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66958 eq314505
  have eq617402 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq17151 eq24950
    | (have j0 := eq24950 (σ y) (σ x)
       grind)
    | exact resolve eq24950 eq17151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17151
  have eq618040 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1466
       have i₂ := eq24950 y x
       grind)
    | exact superpose eq24950 eq1466
    | (have j1 := eq24950 y x
       grind)
    | exact resolve eq1466 eq24950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466 eq24950
  have eq618245 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq618040
  have eq618249 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq617402
  have eq618331 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq618245
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq618245
    | exact resolve eq618245 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618245
  have eq618527 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq618249
    | exact resolve eq618249 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618249
  have eq618618 : x = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq618331
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq618331
    | exact resolve eq618331 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618331
  have eq618619 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq618618
  have eq618655 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq618527
       have r₂ := eq153960
       grind)
    | exact resolve eq618527 eq153960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153960 eq618527
  have eq618717 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq618655
    | exact resolve eq618655 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618655
  have eq618718 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq618717
  have eq618789 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq618718 eq57
    | exact resolve eq57 eq618718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq618999 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq618619 eq618718
    | exact resolve eq618718 eq618619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618619 eq618718
  have eq619016 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq618999
       have r₂ := eq27
       grind)
    | exact resolve eq618999 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618999
  have eq735519 : (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18528 y
       have i₂ := eq618789
       grind)
    | exact superpose eq618789 eq18528
    | (have j0 := eq18528 y
       grind)
    | exact resolve eq18528 eq618789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18528 eq618789
  have eq735856 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq735519
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq735519
    | exact resolve eq735519 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735519
  have eq735877 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq735856
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq735856
    | exact resolve eq735856 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735856
  have eq735887 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq735877
    | exact resolve eq735877 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735877
  have eq735890 : x = (M.op x y) ∨ (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq735887
       have r₂ := eq27
       grind)
    | exact resolve eq735887 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735887
  have eq735893 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq735890
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq735890
    | exact resolve eq735890 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735890
  have eq735932 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq619016
       have i₂ := eq735893
       grind)
    | exact superpose eq735893 eq619016
    | exact resolve eq619016 eq735893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619016 eq735893
  have eq736497 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq735932
  have eq737515 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq736497 eq15
    | exact resolve eq15 eq736497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736497
  have eq737796 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq737515
    | exact resolve eq737515 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737515
  have eq737814 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq737796
       have r₂ := eq27
       grind)
    | exact resolve eq737796 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737796
  have eq738039 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (σ x)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq737814 eq314533
    | exact resolve eq314533 eq737814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314533 eq737814
  have eq738074 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3821 eq738039
    | exact resolve eq738039 eq3821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3821 eq738039
  have eq738807 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq738074 eq3939
    | exact resolve eq3939 eq738074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3939 eq738074
  have eq739293 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq738807
    | exact resolve eq738807 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq738807
  have eq739473 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq739293
    | exact resolve eq739293 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq739293
  have eq739578 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq739473
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq739473
    | exact resolve eq739473 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq739473
  have eq739579 : x = (M.op x y) := by grind
  clear eq739578
  have eq739715 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq739579 eq20
    | exact resolve eq20 eq739579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq740084 : x = (M.op x (M.op (M.op x x) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq739579 eq158377
    | exact resolve eq158377 eq739579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158377 eq739579
  have eq740206 : x = (M.op y y) := by
    first
    | (have i₁ := eq740084
       have i₂ := eq641 y y x x
       grind)
    | exact superpose eq641 eq740084
    | exact resolve eq740084 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641 eq740084
  have eq740375 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq739715
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq739715
    | exact resolve eq739715 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739715
  have eq743160 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3937 y
       have i₂ := eq740206
       grind)
    | exact superpose eq740206 eq3937
    | exact resolve eq3937 eq740206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3937 eq740206
  have eq743695 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq743160
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq743160
    | exact resolve eq743160 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq743160
  have eq743968 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq743695
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq743695
    | exact resolve eq743695 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq743695
  have eq744128 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq743968
    | exact resolve eq743968 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq743968
  have eq744198 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq740375 eq744128
    | exact resolve eq744128 eq740375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740375 eq744128
  have eq744244 : False := by grind
  exact eq744244

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_pxy_pxx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  clear eq35
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq67
    | (have j0 := eq67 (σ X0) (σ X1)
       grind)
    | exact resolve eq67 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq67 x y
       grind)
    | exact superpose eq67 eq44
    | (have j1 := eq67 x y
       grind)
    | exact resolve eq44 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq95
    | exact resolve eq95 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq99 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq67 y y
       grind)
    | exact superpose eq67 eq74
    | (have j1 := eq67 y y
       grind)
    | exact resolve eq74 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq98 eq67
    | (have j0 := eq67 (σ x) (σ y)
       grind)
    | exact resolve eq67 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq118
    | exact resolve eq118 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq122 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq119
       have r₂ := eq27
       grind)
    | exact resolve eq119 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq124 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq122
    | exact resolve eq122 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq136 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  clear eq37
  have eq176 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq67 sF3 sF3
       grind)
    | exact superpose eq67 eq104
    | (have j1 := eq67 (σ y) (σ y)
       grind)
    | exact resolve eq104 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq50 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 X0)) ≠ X0 ∨ (k y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq50 eq13
    | exact resolve eq13 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op X0 X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq124 eq51
    | exact resolve eq51 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq51 (M.op sF4 sF4)
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq224 (M.op sF2 sF2)
       have i₂ := eq14 sF2 sF2 sF2
       grind)
    | exact superpose eq14 eq224
    | exact resolve eq224 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq224 eq14
    | exact resolve eq14 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq232 eq53
    | exact resolve eq53 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq341 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq13
    | (have j0 := eq13 X0 (M.op X1 X0)
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       have i₂ := eq337 (M.op X0 X0) x
       grind)
    | exact superpose eq337 eq14
    | exact resolve eq14 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq390 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq375 X0
       have i₂ := eq53 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq53 eq375
    | exact resolve eq375 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq392 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq390 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq390
    | exact resolve eq390 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq443 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq52 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq489 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq53 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq52 X0 x x X3
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq495 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq506 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq495 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq495
    | exact resolve eq495 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq576 : ∀ X0 X1 X2 : G, (M.op (σ X1) (M.op (σ (k X0 X1)) (M.op X2 X2))) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (σ X1) (σ X0)
       have i₂ := eq81 X0 X1
       grind)
    | exact superpose eq81 eq14
    | (have j1 := eq81 X0 X1
       grind)
    | exact resolve eq14 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq793 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq225 eq224
    | exact resolve eq224 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1812 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq228 eq224
    | exact resolve eq224 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq1840 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq225 eq1812
    | exact resolve eq1812 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq1812
  have eq1884 : (M.op (σ y) (M.op (σ x) (σ x))) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq124 eq1840
    | exact resolve eq1840 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1840
  have eq1897 : (M.op (σ y) (M.op (σ x) (σ x))) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq1884
  have eq2457 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq443 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq443 X0 X0 X0
       grind)
    | exact superpose eq443 eq443
    | exact resolve eq443 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2498 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq443 X0 X0 X0
       grind)
    | exact superpose eq443 eq14
    | exact resolve eq14 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2499 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq443 X0 X0 X0
       grind)
    | exact superpose eq443 eq50
    | exact resolve eq50 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq2506 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq224 (M.op X0 (M.op X0 X0))
       have i₂ := eq443 X0 X0 X0
       grind)
    | exact superpose eq443 eq224
    | exact resolve eq224 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq2513 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq341 (M.op x (M.op x x))
       have i₂ := eq443 x x x
       grind)
    | exact superpose eq443 eq341
    | exact resolve eq341 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq2807 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq351 X0
       have i₂ := eq2506 X0
       grind)
    | exact superpose eq2506 eq351
    | exact resolve eq351 eq2506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2892 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2807
    | (have j0 := eq2807 (σ y)
       grind)
    | exact resolve eq2807 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2807
  have eq2944 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq124 eq2892
    | exact resolve eq2892 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq2892
  have eq2956 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq2944
  have eq2958 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq229 eq2956
    | exact resolve eq2956 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq2956
  have eq2970 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq2958
  have eq2976 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2970 eq1897
    | exact resolve eq1897 eq2970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897
  have eq2986 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (σ y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2970 eq443
    | exact resolve eq443 eq2970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2970
  have eq3004 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq2976
  have eq3009 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2986 x
       have i₂ := eq489 sF3 x
       grind)
    | exact superpose eq489 eq2986
    | exact resolve eq2986 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2986
  have eq3040 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3009 eq2506
    | exact resolve eq2506 eq3009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2506
  have eq3043 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3009 eq13
    | exact resolve eq13 eq3009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3053 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq3040
  have eq3064 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq3053
    | exact resolve eq3053 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3053
  have eq3338 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (M.op (σ y) (σ x)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3064 eq793
    | exact resolve eq793 eq3064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793 eq3064
  have eq3369 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (M.op (σ y) (σ x)))) ∨ x = (M.op x y) := by grind
  clear eq3338
  have eq5555 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3004 eq3369
    | exact resolve eq3369 eq3004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3004 eq3369
  have eq5578 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq5555
  have eq6194 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op (M.op x y) X0) ∨ (M.op X0 (M.op X0 X0)) = (k y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq222 (M.op x (M.op x x))
       have i₂ := eq443 x x x
       grind)
    | exact superpose eq443 eq222
    | exact resolve eq222 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq9603 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op (M.op X2 X3) (M.op X1 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq472 (M.op X0 X1) X1 X2 X3 X1
       have i₂ := eq357 X1 X0 X1 X0
       grind)
    | exact superpose eq357 eq472
    | exact resolve eq472 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq10615 : ∀ X0 : G, (M.op (σ y) (M.op (k (σ y) (σ y)) (M.op X0 X0))) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq576 y y X0
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq576
    | (have j0 := eq576 y y x
       grind)
    | exact resolve eq576 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10620 : ∀ X0 : G, (M.op (σ y) (M.op (k (σ (M.op x y)) (σ y)) (M.op X0 X0))) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq136 eq576
    | (have j0 := eq576 (M.op x y) y x
       grind)
    | exact resolve eq576 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq576
  have eq10673 : ∀ X0 : G, (M.op (σ y) (M.op (k (σ (M.op x y)) (σ y)) (M.op X0 X0))) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10620 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10620
    | (have j0 := eq10620 X0
       grind)
    | exact resolve eq10620 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10620
  have eq10678 : ∀ X0 : G, (M.op (σ y) (M.op (k (σ y) (σ y)) (M.op X0 X0))) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10615 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10615
    | (have j0 := eq10615 X0
       grind)
    | exact resolve eq10615 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10615
  have eq10702 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ y) (M.op (k (σ (M.op x y)) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq10673 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10673
    | (have j0 := eq10673 X0
       grind)
    | exact resolve eq10673 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10673
  have eq10707 : ∀ X0 : G, (M.op (σ y) (M.op (k (σ y) (σ y)) (M.op X0 X0))) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10678 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10678
    | (have j0 := eq10678 X0
       grind)
    | exact resolve eq10678 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq10678
  have eq10726 : ∀ X0 : G, (M.op (σ y) (M.op (k (σ (M.op x y)) (σ y)) (M.op X0 X0))) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq10702
    | (have j0 := eq10702 X0
       grind)
    | exact resolve eq10702 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10702
  have eq24992 : ∀ X0 X1 X2 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X2 (M.op y (M.op y y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2499 eq472
    | exact resolve eq472 eq2499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25043 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq24992 x x x
       have i₂ := eq472 y y x x x
       grind)
    | exact superpose eq472 eq24992
    | exact resolve eq24992 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24992
  have eq25355 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2513 (M.op (M.op x sF0) (M.op X0 X0))
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq2513
    | exact resolve eq2513 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2513
  have eq25489 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq25355 X0 X1
       have i₂ := eq2499 (M.op (M.op X1 sF0) (M.op X0 X0))
       grind)
    | exact superpose eq2499 eq25355
    | exact resolve eq25355 eq2499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2499 eq25355
  have eq25520 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25489 X0 x
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq25489
    | exact resolve eq25489 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25489
  have eq61188 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq472 X0 (M.op X1 X0) X2 X3 X4
       have i₂ := eq2498 X0 X0 X1
       grind)
    | exact superpose eq2498 eq472
    | exact resolve eq472 eq2498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2498
  have eq61287 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61188 X0 X1 x x x
       have i₂ := eq472 X0 X0 x x x
       grind)
    | exact superpose eq472 eq61188
    | exact resolve eq61188 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472 eq61188
  have eq105543 : ∀ X0 : G, (M.op (M.op (k (σ y) (σ y)) (M.op X0 X0)) X0) ≠ X0 ∨ (k X0 X0) = (M.op (M.op (k (σ y) (σ y)) (M.op X0 X0)) X0) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq10707 eq355
    | exact resolve eq355 eq10707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10707
  have eq105614 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = (M.op (M.op (k (σ y) (σ y)) (M.op X0 X0)) X0) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq105543 X0
       have i₂ := eq489 X0 (k sF3 sF3)
       grind)
    | exact superpose eq489 eq105543
    | (have j0 := eq105543 X0
       grind)
    | exact resolve eq105543 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105543
  have eq105638 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) ≠ X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq105614 X0
       have i₂ := eq489 X0 (k sF3 sF3)
       grind)
    | exact superpose eq489 eq105614
    | (have j0 := eq105614 X0
       grind)
    | exact resolve eq105614 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105614
  have eq105646 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq105638 X0
       have j1 := eq67 X0 X0
       grind)
    | (have r₁ := eq105638 x
       have r₂ := eq67 x x
       grind)
    | exact resolve eq105638 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105638
  have eq105861 : ∀ X0 : G, (M.op (M.op (k (σ (M.op x y)) (σ y)) (M.op X0 X0)) X0) ≠ X0 ∨ (k X0 X0) = (M.op (M.op (k (σ (M.op x y)) (σ y)) (M.op X0 X0)) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq10726 eq355
    | exact resolve eq355 eq10726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355 eq10726
  have eq105932 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = (M.op (M.op (k (σ (M.op x y)) (σ y)) (M.op X0 X0)) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq105861 X0
       have i₂ := eq489 X0 (k sF1 sF3)
       grind)
    | exact superpose eq489 eq105861
    | (have j0 := eq105861 X0
       grind)
    | exact resolve eq105861 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105861
  have eq105956 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) ≠ X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq105932 X0
       have i₂ := eq489 X0 (k sF1 sF3)
       grind)
    | exact superpose eq489 eq105932
    | (have j0 := eq105932 X0
       grind)
    | exact resolve eq105932 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105932
  have eq105964 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have j0 := eq105956 X0
       have j1 := eq67 X0 X0
       grind)
    | (have r₁ := eq105956 x
       have r₂ := eq67 x x
       grind)
    | exact resolve eq105956 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq105956
  have eq137295 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op (M.op X1 X2) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) X0) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9603 (M.op X0 X0) (M.op X0 (M.op X0 X0)) X2 x
       have i₂ := eq392 X0
       grind)
    | exact superpose eq392 eq9603
    | exact resolve eq9603 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392 eq9603
  have eq138751 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op (M.op X1 X2) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) X0) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq137295 X0 X1 X2
       have i₂ := eq53 X0 (M.op X0 X0)
       grind)
    | exact superpose eq53 eq137295
    | exact resolve eq137295 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq137295
  have eq139152 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op (M.op X1 X2) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0)))) X0) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq138751 X0 X1 X2
       have i₂ := eq506 X0 X0
       grind)
    | exact superpose eq506 eq138751
    | exact resolve eq138751 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138751
  have eq139342 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op (M.op X1 X2) X0) X0) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq139152
    | exact resolve eq139152 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139152
  have eq139395 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X0) X0) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq139342 X0 X1 X2
       have i₂ := eq489 X0 X0
       grind)
    | exact superpose eq489 eq139342
    | exact resolve eq139342 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489 eq139342
  have eq139418 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq139395 X1 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq351 X0
       grind)
    | exact superpose eq351 eq139395
    | exact resolve eq139395 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351 eq139395
  have eq4192293 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3009 eq176
    | exact resolve eq176 eq3009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq3009
  have eq4192870 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq4192293
    | exact resolve eq4192293 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4192293
  have eq4192893 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq4192870
       grind)
    | exact superpose eq4192870 eq74
    | exact resolve eq74 eq4192870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4192870
  have eq4193384 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4192893
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4192893
    | exact resolve eq4192893 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4192893
  have eq4193602 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4193384
       have r₂ := eq3043
       grind)
    | exact resolve eq4193384 eq3043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3043 eq4193384
  have eq4193997 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4193602 eq104
    | exact resolve eq104 eq4193602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4193602
  have eq4194282 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq4193997
    | exact resolve eq4193997 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4193997
  have eq4194327 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq4194282
       have i₂ := eq105646 y
       grind)
    | exact superpose eq105646 eq4194282
    | exact resolve eq4194282 eq105646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105646 eq4194282
  have eq4236418 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq4194327 eq5578
    | exact resolve eq5578 eq4194327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5578 eq4194327
  have eq4238022 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4236418
  have eq4239568 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq139418 y y
       have i₂ := eq4238022
       grind)
    | exact superpose eq4238022 eq139418
    | exact resolve eq139418 eq4238022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139418 eq4238022
  have eq4239701 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4239568
  have eq4239845 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4239701
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4239701
    | exact resolve eq4239701 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4239701
  have eq4239846 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4239845
  have eq4240479 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4239846 eq27
    | exact resolve eq27 eq4239846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4240481 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4239846 eq64
    | (have r₁ := eq64
       have r₂ := eq4239846
       grind)
    | exact resolve eq64 eq4239846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq4239846
  have eq4243313 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4240481
  have eq4253364 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4243313 eq98
    | exact resolve eq98 eq4243313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq4243313
  have eq4253458 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq4253364
  have eq4253479 : x = (M.op x y) := by
    first
    | (have r₁ := eq4253458
       have r₂ := eq4240479
       grind)
    | exact resolve eq4253458 eq4240479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4240479 eq4253458
  have eq4253491 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq4253479 eq20
    | exact resolve eq20 eq4253479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq4253542 : (M.op x x) = (M.op y x) := by
    first
    | exact superpose eq4253479 eq220
    | exact resolve eq220 eq4253479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq4253910 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq4253479 eq25043
    | exact resolve eq25043 eq4253479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25043
  have eq4254083 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq4253910
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4253910
    | exact resolve eq4253910 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4253910
  have eq4254289 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4253491
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4253491
    | exact resolve eq4253491 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4253491
  have eq4254320 : x = (M.op y y) := by
    first
    | exact superpose eq4253479 eq4254083
    | exact resolve eq4254083 eq4253479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4254083
  have eq4254411 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq4254289 eq26
    | exact resolve eq26 eq4254289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq4256239 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq99
       have i₂ := eq4254320
       grind)
    | exact superpose eq4254320 eq99
    | exact resolve eq99 eq4254320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq4256310 : ∀ X0 X1 : G, y = (M.op (M.op X0 (M.op X1 X1)) (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq443 X0 X1 y
       have i₂ := eq4254320
       grind)
    | exact superpose eq4254320 eq443
    | exact resolve eq443 eq4254320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443 eq4254320
  have eq4257782 : y = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq4256310 x x
       have i₂ := eq2457 x x x
       grind)
    | exact superpose eq2457 eq4256310
    | exact resolve eq4256310 eq2457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2457 eq4256310
  have eq4257804 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq4256239
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4256239
    | exact resolve eq4256239 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4256239
  have eq4258200 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq4254289 eq4257804
    | exact resolve eq4257804 eq4254289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4257804
  have eq4284583 : ∀ X0 X1 : G, (M.op X0 (M.op y X0)) = (M.op (M.op X1 x) (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq4253479 eq25520
    | exact resolve eq25520 eq4253479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25520
  have eq4285613 : (M.op (M.op x y) (M.op x x)) ≠ (M.op (M.op x x) (M.op x (M.op y x))) ∨ (k y (M.op (M.op x y) (M.op x x))) = (M.op (M.op x x) (M.op x (M.op y x))) := by
    first
    | (have i₁ := eq6194 (M.op x x)
       have i₂ := eq4284583 x x
       grind)
    | exact superpose eq4284583 eq6194
    | exact resolve eq6194 eq4284583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6194 eq4284583
  have eq4286886 : (M.op (M.op x x) (M.op x (M.op x x))) ≠ (M.op (M.op x y) (M.op x x)) ∨ (k y (M.op (M.op x y) (M.op x x))) = (M.op (M.op x x) (M.op x (M.op y x))) := by
    first
    | (have i₁ := eq4285613
       have i₂ := eq4253542
       grind)
    | exact superpose eq4253542 eq4285613
    | exact resolve eq4285613 eq4253542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4285613
  have eq4287777 : (M.op x (M.op x x)) ≠ (M.op (M.op x x) (M.op x (M.op x x))) ∨ (k y (M.op (M.op x y) (M.op x x))) = (M.op (M.op x x) (M.op x (M.op y x))) := by
    first
    | exact superpose eq4253479 eq4286886
    | exact resolve eq4286886 eq4253479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4286886
  have eq4288464 : (M.op x (M.op x x)) ≠ (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op x x))) ∨ (k y (M.op (M.op x y) (M.op x x))) = (M.op (M.op x x) (M.op x (M.op y x))) := by
    first
    | (have i₁ := eq4287777
       have i₂ := eq506 x x
       grind)
    | exact superpose eq506 eq4287777
    | exact resolve eq4287777 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4287777
  have eq4288973 : x ≠ (M.op x (M.op x x)) ∨ (k y (M.op (M.op x y) (M.op x x))) = (M.op (M.op x x) (M.op x (M.op y x))) := by
    first
    | exact superpose eq51 eq4288464
    | exact resolve eq4288464 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4288464
  have eq4289296 : x ≠ y ∨ (k y (M.op (M.op x y) (M.op x x))) = (M.op (M.op x x) (M.op x (M.op y x))) := by
    first
    | (have i₁ := eq4288973
       have i₂ := eq4257782
       grind)
    | exact superpose eq4257782 eq4288973
    | exact resolve eq4288973 eq4257782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4288973
  have eq4289508 : (M.op (M.op x x) (M.op x (M.op x x))) = (k y (M.op (M.op x y) (M.op x x))) ∨ x ≠ y := by
    first
    | (have i₁ := eq4289296
       have i₂ := eq4253542
       grind)
    | exact superpose eq4253542 eq4289296
    | exact resolve eq4289296 eq4253542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4253542 eq4289296
  have eq4289632 : (k y (M.op x (M.op x x))) = (M.op (M.op x x) (M.op x (M.op x x))) ∨ x ≠ y := by
    first
    | exact superpose eq4253479 eq4289508
    | exact resolve eq4289508 eq4253479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4289508
  have eq4289688 : (k y (M.op x (M.op x x))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op x x))) ∨ x ≠ y := by
    first
    | (have i₁ := eq4289632
       have i₂ := eq506 x x
       grind)
    | exact superpose eq506 eq4289632
    | exact resolve eq4289632 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506 eq4289632
  have eq4289721 : x = (k y (M.op x (M.op x x))) ∨ x ≠ y := by
    first
    | exact superpose eq51 eq4289688
    | exact resolve eq4289688 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq4289688
  have eq4289749 : x ≠ y ∨ x = (k y y) := by
    first
    | (have i₁ := eq4289721
       have i₂ := eq4257782
       grind)
    | exact superpose eq4257782 eq4289721
    | exact resolve eq4289721 eq4257782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4257782 eq4289721
  have eq4293933 : (τ (σ (M.op x y))) = (k y y) ∨ x = y := by
    first
    | exact superpose eq4258200 eq104
    | exact resolve eq104 eq4258200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq4258200
  have eq4294291 : (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq30 eq4293933
    | exact resolve eq4293933 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4293933
  have eq4294387 : x = (k y y) ∨ x = y := by
    first
    | exact superpose eq4253479 eq4294291
    | exact resolve eq4294291 eq4253479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4253479 eq4294291
  have eq4294425 : x = (k y y) := by
    first
    | (have r₁ := eq4294387
       have r₂ := eq4289749
       grind)
    | exact resolve eq4294387 eq4289749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4289749 eq4294387
  have eq4294465 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq4294425
       grind)
    | exact superpose eq4294425 eq74
    | exact resolve eq74 eq4294425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq4294425
  have eq4294958 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq4294465
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4294465
    | exact resolve eq4294465 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4294465
  have eq4295195 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq4254289 eq4294958
    | exact resolve eq4294958 eq4254289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4254289 eq4294958
  have eq4296259 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq4295195 eq105964
    | exact resolve eq105964 eq4295195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105964 eq4295195
  have eq4296376 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq4254411 eq4296259
    | exact resolve eq4296259 eq4254411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4296259
  have eq4296501 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq4296376
       have r₂ := eq27
       grind)
    | exact resolve eq4296376 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4296376
  have eq4297764 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq4296501 eq61287
    | exact resolve eq61287 eq4296501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61287 eq4296501
  have eq4297994 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4254411 eq4297764
    | exact resolve eq4297764 eq4254411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4254411 eq4297764
  have eq4298625 : False := by grind
  exact eq4298625

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pxy_x_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  clear eq35
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq66 (σ X0)
       grind)
    | exact superpose eq66 eq10
    | exact resolve eq10 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq68
    | exact resolve eq68 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq85 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
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
  have eq92 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq94 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq92
       have i₂ := eq66 sF3
       grind)
    | exact superpose eq66 eq92
    | exact resolve eq92 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq96 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq94
       have i₂ := eq66 y
       grind)
    | exact superpose eq66 eq94
    | exact resolve eq94 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq85 x y
       grind)
    | exact superpose eq85 eq44
    | (have j1 := eq85 x y
       grind)
    | exact resolve eq44 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq127 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq124
    | exact resolve eq124 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq132 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq16
    | exact resolve eq16 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq151 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq148
       have i₂ := eq66 sF1
       grind)
    | exact superpose eq66 eq148
    | exact resolve eq148 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq153 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq151
       have i₂ := eq66 sF0
       grind)
    | exact superpose eq66 eq151
    | exact resolve eq151 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq151
  have eq239 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq50 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : (σ (M.op y (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq239 eq153
    | exact resolve eq153 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq239
  have eq510 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq73 (M.op y y)
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq73
    | exact resolve eq73 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq603 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (σ y) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq567
       have i₂ := eq53 sF3 sF3
       grind)
    | exact superpose eq53 eq567
    | exact resolve eq567 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq609 : (M.op (σ y) (M.op (σ y) (σ y))) = (σ (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq603
       have i₂ := eq53 y y
       grind)
    | exact superpose eq53 eq603
    | exact resolve eq603 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq710 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq52 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X1 X1) X1 X2 X1
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq746 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    by_contra hcon
    push Not at hcon
    have f746_11 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
      intro X0 X1
      grind
    have f746_12 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
      intro X0 X1 X2 X3
      grind
    have f746_20 : (M.op X0 X0) ≠ (M.op (M.op X3 (M.op X0 X0)) X0) := by grind
    have f746_58 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
      intro X0 X3
      first
      | (have i₁ := f746_11 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
         have i₂ := f746_12 X0 x x X3
         grind)
      | exact superpose f746_12 f746_11
      | exact resolve f746_11 f746_12
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f746_108 : (M.op X0 X0) ≠ (M.op X0 X0) := by
      first
      | (have i₁ := f746_20
         have i₂ := f746_58 X0 X3
         grind)
      | exact superpose f746_58 f746_20
      | (have r₁ := f746_20
         have r₂ := f746_58 X0 X3
         grind)
      | exact resolve f746_20 f746_58
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f746_114 : False := by grind
    exact f746_114
  clear eq52
  have eq993 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq127 eq85
    | (have j0 := eq85 (σ x) (σ y)
       grind)
    | exact resolve eq85 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq994 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq993
    | exact resolve eq993 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq997 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq994
       have r₂ := eq27
       grind)
    | exact resolve eq994 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994
  have eq1000 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq997 eq53
    | exact resolve eq53 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1001 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq997 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq997
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq997
       grind)
    | exact resolve eq12 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq1003 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq1001
  have eq1004 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq1000
    | exact resolve eq1000 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000
  have eq1755 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1003 eq1004
    | exact resolve eq1004 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq1756 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1003 eq132
    | exact resolve eq132 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq1003
  have eq1782 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1755
  have eq1786 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq1756
    | exact resolve eq1756 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1756
  have eq1841 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq710 X0 X0 X0
       grind)
    | exact superpose eq710 eq50
    | exact resolve eq50 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1853 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq746 (M.op x (M.op x x)) x
       have i₂ := eq710 x x x
       grind)
    | exact superpose eq710 eq746
    | exact resolve eq746 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq1902 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1782 eq127
    | exact resolve eq127 eq1782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1903 : (τ (σ x)) = (k x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1782 eq57
    | exact resolve eq57 eq1782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1782
  have eq1905 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1902
  have eq1907 : y = (M.op y x) ∨ x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq1903
    | exact resolve eq1903 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1903
  have eq1911 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq1905
       grind)
    | exact superpose eq1905 eq53
    | exact resolve eq53 eq1905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1905
  have eq1917 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1911
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1911
    | exact resolve eq1911 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1911
  have eq1921 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq96
       have i₂ := eq1917
       grind)
    | exact superpose eq1917 eq96
    | exact resolve eq96 eq1917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1917
  have eq1952 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1921
    | exact resolve eq1921 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1921
  have eq1986 : y ≠ y ∨ y = (M.op y y) ∨ x = (k x y) ∨ x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1907
       grind)
    | exact superpose eq1907 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1907
       grind)
    | exact resolve eq12 eq1907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1907
  have eq1992 : y ≠ y ∨ y = (M.op y y) ∨ x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1986
  have eq1993 : y = (M.op y y) ∨ x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1992
  have eq2019 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq96
       have i₂ := eq1993
       grind)
    | exact superpose eq1993 eq96
    | exact resolve eq96 eq1993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2020 : ∀ X0 : G, y ≠ (M.op y X0) ∨ (k X0 y) = (M.op X0 y) ∨ x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1993
       grind)
    | exact superpose eq1993 eq13
    | (have j0 := eq13 X0 y
       grind)
    | exact resolve eq13 eq1993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1993
  have eq2048 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2020 X0
       have j1 := eq85 X0 y
       grind)
    | (have r₁ := eq2020 X0
       have r₂ := eq85 X0 y
       grind)
    | exact resolve eq2020 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2020
  have eq2049 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2019
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2019
    | exact resolve eq2019 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2019
  have eq3452 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1786 eq127
    | exact resolve eq127 eq1786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786
  have eq3455 : y = (M.op y y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3452
  have eq3523 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq3455
       grind)
    | exact superpose eq3455 eq96
    | exact resolve eq96 eq3455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3455
  have eq3564 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3523
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3523
    | exact resolve eq3523 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3523
  have eq3733 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq3564 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | exact resolve eq13 eq3564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3564
  have eq3773 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq3733 X0
       have j1 := eq85 X0 (σ y)
       grind)
    | (have r₁ := eq3733 X0
       have r₂ := eq85 X0 (σ y)
       grind)
    | exact resolve eq3733 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3733
  have eq4559 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq510 X0 X0 (M.op X0 X0) x
       have i₂ := eq710 x X0 X0
       grind)
    | exact superpose eq710 eq510
    | exact resolve eq510 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510 eq710
  have eq11755 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq2048 x
       grind)
    | exact superpose eq2048 eq44
    | exact resolve eq44 eq2048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048
  have eq11781 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11755
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11755
    | exact resolve eq11755 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11755
  have eq11783 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq11781
    | exact resolve eq11781 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11781
  have eq11801 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11783 eq85
    | (have j0 := eq85 (σ x) (σ y)
       grind)
    | exact resolve eq85 eq11783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11783
  have eq11808 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11801
    | exact resolve eq11801 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11801
  have eq11811 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11808
       have r₂ := eq27
       grind)
    | exact resolve eq11808 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11808
  have eq11838 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11811 eq53
    | exact resolve eq53 eq11811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11811
  have eq11867 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11838
    | exact resolve eq11838 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11838
  have eq12750 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11867 eq2049
    | exact resolve eq2049 eq11867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049 eq11867
  have eq12825 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12750
  have eq12860 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq12825
       grind)
    | exact superpose eq12825 eq44
    | exact resolve eq44 eq12825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12825
  have eq12868 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12860
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12860
    | exact resolve eq12860 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12860
  have eq13533 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12868 eq85
    | (have j0 := eq85 (σ y) (σ x)
       grind)
    | exact resolve eq85 eq12868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12868
  have eq13536 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13533
    | exact resolve eq13533 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13533
  have eq14137 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13536 eq53
    | exact resolve eq53 eq13536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13536
  have eq14171 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq14137
    | exact resolve eq14137 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14137
  have eq14295 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14171 eq1952
    | exact resolve eq1952 eq14171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952 eq14171
  have eq14376 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14295
  have eq14398 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq14376
       have r₂ := eq27
       grind)
    | exact resolve eq14376 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14376
  have eq14549 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14398 eq27
    | exact resolve eq27 eq14398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14398
  have eq22302 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3773 eq127
    | exact resolve eq127 eq3773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq3773
  have eq22330 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq22302
  have eq22340 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq22330
    | exact resolve eq22330 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22330
  have eq22343 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq22340
       have r₂ := eq27
       grind)
    | exact resolve eq22340 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22340
  have eq22346 : y ≠ y ∨ y = (M.op y y) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq22343
       grind)
    | exact superpose eq22343 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq22343
       grind)
    | exact resolve eq12 eq22343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22349 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq22343
       grind)
    | exact superpose eq22343 eq53
    | exact resolve eq53 eq22343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22343
  have eq22382 : y = (M.op y y) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq22346
  have eq22391 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22349
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22349
    | exact resolve eq22349 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22349
  have eq22406 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq22391
       grind)
    | exact superpose eq22391 eq96
    | exact resolve eq96 eq22391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22391
  have eq22521 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq22406
    | exact resolve eq22406 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq22406
  have eq22631 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op (M.op X1 X0) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq22521 eq14
    | exact resolve eq14 eq22521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25773 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22631 sF1 sF1
       have i₂ := eq4559 sF1
       grind)
    | exact superpose eq4559 eq22631
    | exact resolve eq22631 eq4559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22631
  have eq25952 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 X1) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq25773 eq741
    | exact resolve eq741 eq25773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741 eq25773
  have eq32061 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq25952 x (M.op (M.op x x) (M.op X0 X0))
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq25952
    | exact resolve eq25952 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25952
  have eq32755 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq32061
    | (have j0 := eq32061 (σ x)
       grind)
    | exact resolve eq32061 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32061
  have eq35499 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq22382
       grind)
    | exact superpose eq22382 eq96
    | exact resolve eq96 eq22382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq22382
  have eq35643 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq35499
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35499
    | exact resolve eq35499 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq35499
  have eq35862 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq35643 eq22521
    | exact resolve eq22521 eq35643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35643
  have eq35965 : x = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq35862
  have eq36003 : (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq35965
       grind)
    | exact superpose eq35965 eq44
    | exact resolve eq44 eq35965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq35965
  have eq36023 : (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq36003
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36003
    | exact resolve eq36003 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq36003
  have eq36115 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq36023 eq85
    | (have j0 := eq85 (σ y) (σ x)
       grind)
    | exact resolve eq85 eq36023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq36023
  have eq36123 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq36115
    | exact resolve eq36115 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36115
  have eq36126 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq36123
       have r₂ := eq14549
       grind)
    | exact resolve eq36123 eq14549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14549 eq36123
  have eq36131 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq36126 eq53
    | exact resolve eq53 eq36126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq36126
  have eq36184 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq36131
    | exact resolve eq36131 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36131
  have eq36221 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq36184 eq22521
    | exact resolve eq22521 eq36184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22521 eq36184
  have eq36335 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq36221
  have eq36362 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq36335
       have r₂ := eq27
       grind)
    | exact resolve eq36335 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36335
  have eq36505 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq36362 eq32755
    | exact resolve eq32755 eq36362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32755 eq36362
  have eq36508 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq36505
  have eq36556 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq36508
    | exact resolve eq36508 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36508
  have eq36563 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq36556
       have r₂ := eq27
       grind)
    | exact resolve eq36556 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36556
  have eq36565 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq36563 eq26
    | exact resolve eq26 eq36563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq36566 : x = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq36563 eq28
    | exact resolve eq28 eq36563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq36563
  have eq36614 : x = (M.op x y) := by
    first
    | exact superpose eq30 eq36566
    | exact resolve eq36566 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq36566
  have eq36683 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq36614 eq1841
    | exact resolve eq1841 eq36614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36880 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq36565 eq1853
    | (have j0 := eq1853 (σ y) (σ x)
       grind)
    | exact resolve eq1853 eq36565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853
  have eq36901 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) := by
    first
    | (have i₁ := eq36880
       have i₂ := eq1841 sF3
       grind)
    | exact superpose eq1841 eq36880
    | exact resolve eq36880 eq1841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36880
  have eq36910 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op y (M.op x (σ y)))) := by
    first
    | exact superpose eq36614 eq36901
    | exact resolve eq36901 eq36614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36901
  have eq42345 : (σ (M.op y (M.op y y))) = (M.op y (M.op (M.op x y) (σ y))) := by
    first
    | (have i₁ := eq609
       have i₂ := eq1841 sF3
       grind)
    | exact superpose eq1841 eq609
    | exact resolve eq609 eq1841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609 eq1841
  have eq42346 : (σ (M.op y (M.op y y))) = (M.op y (M.op x (σ y))) := by
    first
    | exact superpose eq36614 eq42345
    | exact resolve eq42345 eq36614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36614 eq42345
  have eq42815 : (M.op y (M.op x (σ y))) = (σ (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq42346
       have i₂ := eq36683 y
       grind)
    | exact superpose eq36683 eq42346
    | exact resolve eq42346 eq36683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36683 eq42346
  have eq42816 : (σ (M.op y (M.op x y))) = (M.op y (M.op x (σ y))) := by
    first
    | (have i₁ := eq42815
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq42815
    | exact resolve eq42815 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq42815
  have eq42817 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op y (M.op x (σ y))) := by
    first
    | exact superpose eq247 eq42816
    | exact resolve eq42816 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq42816
  have eq42818 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq42817 eq36910
    | exact resolve eq36910 eq42817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36910 eq42817
  have eq42894 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq42818 eq51
    | exact resolve eq51 eq42818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq42818
  have eq43090 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq42894 eq4559
    | exact resolve eq4559 eq42894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4559 eq42894
  have eq43159 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36565 eq43090
    | exact resolve eq43090 eq36565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36565 eq43090
  have eq43203 : False := by grind
  exact eq43203

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_x_pyx_pxx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq52 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq10
    | exact resolve eq10 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq50
    | exact resolve eq50 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq71
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq71
    | exact resolve eq71 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq69
    | exact resolve eq69 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op y y) = (M.op y x) := by
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
  clear eq45
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq82
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq82
    | exact resolve eq82 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq88 : (M.op y y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq87
    | exact resolve eq87 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq108 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq112 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq67 sF3
       grind)
    | exact superpose eq67 eq108
    | exact resolve eq108 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq114 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq112
       have i₂ := eq67 y
       grind)
    | exact superpose eq67 eq112
    | exact resolve eq112 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq112
  have eq150 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq114
       grind)
    | exact superpose eq114 eq16
    | exact resolve eq16 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq255 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq52 (M.op sF4 sF4)
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op X1 X0) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq255 eq14
    | exact resolve eq14 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X1 X0)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq53 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq592 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X4 X2 X3 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq53 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq54 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq53 X0 x x X3
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq607 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq53 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq53 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq614 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq609 X0 X1
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq609
    | exact resolve eq609 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq616 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq607 X0 X1 X2 X3
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq607
    | exact resolve eq607 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq623 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq593 X0 X1 X2 X3 X4
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq593
    | exact resolve eq593 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq655 : ∀ X0 : G, (σ X0) = (M.op y (M.op (M.op x y) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq51 (σ X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq51
    | exact resolve eq51 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq2029 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq534 (M.op x sF4) (M.op x sF4)
       have i₂ := eq14 (M.op x sF4) sF4 x
       grind)
    | exact superpose eq14 eq534
    | exact resolve eq534 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2040 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq2029 X0
       have i₂ := eq54 X0 sF4
       grind)
    | exact superpose eq54 eq2029
    | exact resolve eq2029 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2029
  have eq2232 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq565 X1 (M.op X0 (M.op X0 X0)) X2
       have i₂ := eq565 X0 X0 X0
       grind)
    | exact superpose eq565 eq565
    | exact resolve eq565 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2255 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq565 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq565 X0 X0 X0
       grind)
    | exact superpose eq565 eq565
    | exact resolve eq565 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2288 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq565 X0 X0 X0
       grind)
    | exact superpose eq565 eq14
    | exact resolve eq14 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2290 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq565 X0 X0 X0
       grind)
    | exact superpose eq565 eq51
    | exact resolve eq51 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2291 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op X0 (M.op X0 X0))
       have i₂ := eq565 X0 X0 X0
       grind)
    | exact superpose eq565 eq52
    | exact resolve eq52 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2303 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq520 (M.op x (M.op x x))
       have i₂ := eq565 x x x
       grind)
    | exact superpose eq565 eq520
    | exact resolve eq520 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq2307 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq603 (M.op x (M.op x x)) x
       have i₂ := eq565 x x x
       grind)
    | exact superpose eq565 eq603
    | exact resolve eq603 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq2544 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq530 X0
       have i₂ := eq2290 X0
       grind)
    | exact superpose eq2290 eq530
    | exact resolve eq530 eq2290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2574 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq2290 eq534
    | exact resolve eq534 eq2290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2586 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq534 eq2574
    | exact resolve eq2574 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534 eq2574
  have eq2633 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq655 eq2544
    | exact resolve eq2544 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655 eq2544
  have eq2756 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq2291 X0
       have i₂ := eq2290 X0
       grind)
    | exact superpose eq2290 eq2291
    | exact resolve eq2291 eq2290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2291
  have eq2896 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2303 (M.op (M.op x sF0) (M.op X0 X0))
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq2303
    | exact resolve eq2303 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2303
  have eq2950 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2896 X0 X1
       have i₂ := eq2290 (M.op (M.op X1 sF0) (M.op X0 X0))
       grind)
    | exact superpose eq2290 eq2896
    | exact resolve eq2896 eq2290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2896
  have eq2969 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2950 X0 x
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq2950
    | exact resolve eq2950 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2950
  have eq3125 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq27 eq2307
    | (have j0 := eq2307 (σ y) (σ x)
       grind)
    | exact resolve eq2307 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2307
  have eq3195 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) := by
    first
    | (have i₁ := eq3125
       have i₂ := eq2290 sF3
       grind)
    | exact superpose eq2290 eq3125
    | exact resolve eq3125 eq2290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3125
  have eq6988 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq52 eq592
    | exact resolve eq592 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq7049 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq255 eq6988
    | exact resolve eq6988 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6988
  have eq7209 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq616 X0 X1 X2 X3
       have i₂ := eq614 X0 X1
       grind)
    | exact superpose eq614 eq616
    | exact resolve eq616 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq7396 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X1 (M.op X0 X0)))) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq7209 X1 (M.op X0 X0) (M.op X1 X1) x
       have i₂ := eq565 x X1 X0
       grind)
    | exact superpose eq565 eq7209
    | exact resolve eq7209 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq7422 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op X2 X1)) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7209 (M.op X3 (M.op X2 X1)) (M.op X0 X0) X1 X2
       have i₂ := eq14 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq14 eq7209
    | exact resolve eq7209 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7478 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X2 (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X1 X2)) X2 X1
       have i₂ := eq7209 X0 (M.op X1 X2) (M.op X1 X2) X0
       grind)
    | exact superpose eq7209 eq14
    | exact resolve eq14 eq7209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7209
  have eq9373 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq623 X0 X1 X2 X3 X4
       have i₂ := eq614 X0 X1
       grind)
    | exact superpose eq614 eq623
    | exact resolve eq623 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614 eq623
  have eq9507 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) X0)) = (M.op (M.op (M.op X1 X2) (M.op X3 X3)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9373 X0 (M.op X0 (M.op X0 X0)) X2 X3 x
       have i₂ := eq530 X0
       grind)
    | exact superpose eq530 eq9373
    | exact resolve eq9373 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq9373
  have eq35562 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq592 X0 (M.op X1 X0) X2 X3 X4
       have i₂ := eq2288 X0 X0 X1
       grind)
    | exact superpose eq2288 eq592
    | exact resolve eq592 eq2288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35672 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq35562 X0 X1 x x x
       have i₂ := eq592 X0 X0 x x x
       grind)
    | exact superpose eq592 eq35562
    | exact resolve eq35562 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592 eq35562
  have eq37043 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq7049 eq2288
    | exact resolve eq2288 eq7049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2288 eq7049
  have eq37092 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2040 eq37043
    | exact resolve eq37043 eq2040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040 eq37043
  have eq37099 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2756 eq37092
    | exact resolve eq37092 eq2756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2756 eq37092
  have eq51219 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2969 eq14
    | exact resolve eq14 eq2969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2969
  have eq53309 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op y (M.op y y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2232 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2232
    | (have j0 := eq2232 y x X0
       grind)
    | exact resolve eq2232 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2232
  have eq55182 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq2255
    | (have j0 := eq2255 (σ y) X0 (σ x)
       grind)
    | exact resolve eq2255 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55859 : ∀ X0 : G, (M.op y (M.op (M.op x y) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq55182 X0
       have i₂ := eq2290 sF3
       grind)
    | exact superpose eq2290 eq55182
    | exact resolve eq55182 eq2290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290 eq55182
  have eq82451 : y = (M.op (M.op x y) (M.op (M.op y (M.op y x)) (M.op y x))) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq53309 y
       have i₂ := eq88
       grind)
    | exact superpose eq88 eq53309
    | exact resolve eq53309 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq53309
  have eq82621 : y = (M.op (M.op x y) (M.op (M.op y x) (M.op y x))) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq82451
       have i₂ := eq35672 (M.op y x) y
       grind)
    | exact superpose eq35672 eq82451
    | exact resolve eq82451 eq35672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82451
  have eq82661 : y = (M.op (M.op x y) (M.op x (M.op y x))) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq82621
       have i₂ := eq54 y x
       grind)
    | exact superpose eq54 eq82621
    | exact resolve eq82621 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq82621
  have eq82679 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq51219 eq82661
    | exact resolve eq82661 eq51219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51219 eq82661
  have eq114165 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op X0 (M.op X0 X0))) (M.op X2 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7422 X2 (M.op X1 X0) (M.op x (M.op X1 X1)) X3
       have i₂ := eq2255 X0 x X1
       grind)
    | exact superpose eq2255 eq7422
    | exact resolve eq7422 eq2255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2255
  have eq115122 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq7422 eq114165
    | exact resolve eq114165 eq7422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114165
  have eq129269 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq7396 eq7478
    | exact resolve eq7478 eq7396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7396
  have eq129296 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X3)))) = (M.op (M.op (M.op x y) (M.op X0 (M.op X1 X2))) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq7478 eq7422
    | exact resolve eq7422 eq7478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7478
  have eq129520 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op x y) (M.op X0 (M.op X1 X2))) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq7422 eq129296
    | exact resolve eq129296 eq7422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129296
  have eq133438 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op y (M.op (M.op x y) X0))) (M.op X2 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7422 X2 (M.op X1 X0) (M.op (M.op x x) (M.op X1 X1)) X3
       have i₂ := eq9507 X0 x x X1
       grind)
    | exact superpose eq9507 eq7422
    | exact resolve eq7422 eq9507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9507
  have eq133483 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op x y) X0) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq7422 eq133438
    | exact resolve eq133438 eq7422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7422 eq133438
  have eq190739 : (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq55859 eq129269
    | exact resolve eq129269 eq55859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55859 eq129269
  have eq191579 : (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (M.op x y) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq190739
       have i₂ := eq133483 sF2 sF2 (M.op sF4 sF4)
       grind)
    | exact superpose eq133483 eq190739
    | exact resolve eq190739 eq133483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190739
  have eq191952 : (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq255 eq191579
    | exact resolve eq191579 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq191579
  have eq192145 : (σ y) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3195 eq191952
    | exact resolve eq191952 eq3195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3195 eq191952
  have eq192871 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq192145
       have i₂ := eq133483 sF2 sF0 (M.op sF3 sF4)
       grind)
    | exact superpose eq133483 eq192145
    | exact resolve eq192145 eq133483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192145
  have eq293852 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq82679 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq82679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82679
  have eq293853 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq293852
    | exact resolve eq293852 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293852
  have eq293864 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq293853
       have r₂ := eq28
       grind)
    | exact resolve eq293853 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293853
  have eq293884 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq293864 eq37099
    | exact resolve eq37099 eq293864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37099
  have eq294067 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq293864 eq264
    | exact resolve eq264 eq293864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq294147 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op (M.op x y) (M.op X1 (M.op (σ y) (σ x)))) X0) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq293864 eq129520
    | exact resolve eq129520 eq293864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294161 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by grind
  have eq294173 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq129520 eq294147
    | exact resolve eq294147 eq129520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129520 eq294147
  have eq294213 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ x)) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq294067
       have i₂ := eq115122 sF2 sF3 (M.op sF3 sF4)
       grind)
    | exact superpose eq115122 eq294067
    | exact resolve eq294067 eq115122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294067
  have eq294325 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq293884
       have i₂ := eq115122 sF2 sF3 (M.op sF3 sF4)
       grind)
    | exact superpose eq115122 eq293884
    | exact resolve eq293884 eq115122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115122 eq293884
  have eq294357 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (M.op x y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq294213
       have i₂ := eq133483 sF2 sF2 (M.op sF3 sF4)
       grind)
    | exact superpose eq133483 eq294213
    | exact resolve eq294213 eq133483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294213
  have eq294420 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq294325
       have i₂ := eq133483 sF2 sF2 (M.op sF3 sF4)
       grind)
    | exact superpose eq133483 eq294325
    | exact resolve eq294325 eq133483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133483 eq294325
  have eq294427 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq192871 eq294357
    | exact resolve eq294357 eq192871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294357
  have eq294453 : (σ y) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq192871 eq294420
    | exact resolve eq294420 eq192871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192871 eq294420
  have eq294462 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq293864 eq294427
    | exact resolve eq294427 eq293864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293864 eq294427
  have eq294758 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq294462
  have eq294886 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq294758
       have r₂ := eq294161
       grind)
    | exact resolve eq294758 eq294161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294161 eq294758
  have eq299229 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq294173 eq294886
    | exact resolve eq294886 eq294173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294173 eq294886
  have eq299880 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq299229
  have eq303633 : (σ x) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq299880 eq51
    | exact resolve eq51 eq299880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq299880
  have eq317490 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = y ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq303633 eq294453
    | exact resolve eq294453 eq303633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294453 eq303633
  have eq317636 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by grind
  clear eq317490
  have eq317788 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq317636 eq150
    | exact resolve eq150 eq317636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq317636
  have eq318236 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq29 eq317788
    | exact resolve eq317788 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317788
  have eq318237 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq318236
  have eq318655 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq35672 y y
       have i₂ := eq318237
       grind)
    | exact superpose eq318237 eq35672
    | exact resolve eq35672 eq318237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35672 eq318237
  have eq318697 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq318655
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq318655
    | exact resolve eq318655 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318655
  have eq318978 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq318697 eq30
    | exact resolve eq30 eq318697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq318697
  have eq319347 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq318978
    | exact resolve eq318978 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq318978
  have eq319348 : x = (M.op x y) ∨ x = y := by grind
  clear eq319347
  have eq319400 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq319348 eq21
    | exact resolve eq21 eq319348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319522 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq319348 eq2586
    | exact resolve eq2586 eq319348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2586 eq319348
  have eq319896 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq319522
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq319522
    | exact resolve eq319522 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319522
  have eq319966 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq319400
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq319400
    | exact resolve eq319400 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319400
  have eq320024 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq319966 eq27
    | exact resolve eq27 eq319966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319966
  have eq320394 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2633 y
       have i₂ := eq319896
       grind)
    | exact superpose eq319896 eq2633
    | exact resolve eq2633 eq319896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2633 eq319896
  have eq320644 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq320394
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq320394
    | exact resolve eq320394 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320394
  have eq320752 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq320644
    | exact resolve eq320644 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320644
  have eq321648 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq320752 eq320024
    | exact resolve eq320024 eq320752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320024 eq320752
  have eq321758 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq321648
  have eq321809 : x = y := by
    first
    | (have r₁ := eq321758
       have r₂ := eq28
       grind)
    | exact resolve eq321758 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321758
  have eq321836 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq321809
       grind)
    | exact superpose eq321809 eq19
    | exact resolve eq19 eq321809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq321837 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq321809
       grind)
    | exact superpose eq321809 eq25
    | exact resolve eq25 eq321809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq321809
  have eq322381 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq321837
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq321837
    | exact resolve eq321837 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq321837
  have eq322473 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq322381 eq27
    | exact resolve eq27 eq322381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq322381
  have eq323805 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq322473 eq72
    | exact resolve eq72 eq322473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq322473
  have eq324284 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq323805
       have i₂ := eq321836
       grind)
    | exact superpose eq321836 eq323805
    | exact resolve eq323805 eq321836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321836 eq323805
  have eq324527 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq324284 eq15
    | exact resolve eq15 eq324284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324284
  have eq324899 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq324527
    | exact resolve eq324527 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq324527
  have eq325034 : False := by grind
  exact eq325034

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_x_pxy_pyx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq31 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X2) (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq31
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq9
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X3 (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) X3 X2
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq9
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq66 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq9
    | exact resolve eq9 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 (M.op X1 (M.op X1 X1)) X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq79
    | (have j0 := eq79 (σ X0) (σ X1)
       grind)
    | exact resolve eq79 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 X2))) = X2 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 X1
       have i₂ := eq79 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq79 (M.op X2 X1) X1
       grind)
    | exact superpose eq79 eq9
    | (have j1 := eq79 X0 X1
       grind)
    | exact resolve eq9 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X1
       have i₂ := eq79 X0 X1
       grind)
    | (have i₁ := eq59 X0
       have i₂ := eq79 (M.op X0 X0) X1
       grind)
    | exact superpose eq79 eq59
    | (have j1 := eq79 X0 X1
       grind)
    | exact resolve eq59 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq95 : ∀ X1 X3 : G, (M.op X3 X3) = (M.op (M.op X1 (M.op X3 X3)) X3) := by
    intro X1 X3
    first
    | (have i₁ := eq57 x X3 (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq57
    | exact resolve eq57 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq138 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X1 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X0 X0))
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq9
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    have f139_10 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
      intro X0 X1
      grind
    have f139_11 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
      intro X0 X1
      grind
    have f139_18 : X0 ≠ (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) := by grind
    have f139_40 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
      intro X0 X1
      first
      | (have i₁ := f139_10 X0 (M.op X1 (M.op X1 X1))
         have i₂ := f139_11 X1 X1
         grind)
      | exact superpose f139_11 f139_10
      | exact resolve f139_10 f139_11
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f139_84 : X0 ≠ X0 := by
      first
      | (have i₁ := f139_18
         have i₂ := f139_40 X0 X1
         grind)
      | exact superpose f139_40 f139_18
      | (have r₁ := f139_18
         have r₂ := f139_40 X0 X1
         grind)
      | exact resolve f139_18 f139_40
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f139_87 : False := by grind
    exact f139_87
  clear eq66 eq95
  have eq347 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1 X0
       have i₂ := eq89 X0 X0
       grind)
    | exact superpose eq89 eq86
    | (have j0 := eq86 X0 X1 x
       have j1 := eq89 X0 X1
       grind)
    | exact resolve eq86 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq89
  have eq369 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq347 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq347 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq347 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq382 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq369 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq383 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq382 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq387 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq383 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq383
    | exact resolve eq383 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq387 X0
       have i₂ := eq383 X0
       grind)
    | exact superpose eq383 eq387
    | exact resolve eq387 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383 eq387
  have eq718 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 X1
       have i₂ := eq390 X1
       grind)
    | exact superpose eq390 eq82
    | (have j0 := eq82 X0 X1
       grind)
    | exact resolve eq82 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq870 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq718 x y
       grind)
    | exact superpose eq718 eq16
    | (have j1 := eq718 x y
       grind)
    | exact resolve eq16 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq1590 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 (M.op X0 X0) X2 X1
       have i₂ := eq139 X0 X0
       grind)
    | exact superpose eq139 eq62
    | exact resolve eq62 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq1593 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq62 X0 X0 x (M.op X0 X0)
       have i₂ := eq138 x X0 X0
       grind)
    | exact superpose eq138 eq62
    | exact resolve eq62 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq1648 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1593 (σ X0)
       have i₂ := eq390 X0
       grind)
    | exact superpose eq390 eq1593
    | exact resolve eq1593 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq1593
  have eq1836 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op X3 X2) (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 (M.op X0 X1) X1 X3 X2
       have i₂ := eq1590 X1 X1 X0
       grind)
    | exact superpose eq1590 eq62
    | exact resolve eq62 eq1590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1590
  have eq1856 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1836 X0 X1 x x
       have i₂ := eq62 X1 X1 x x
       grind)
    | exact superpose eq62 eq1836
    | exact resolve eq1836 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq1836
  have eq3259 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq870
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq870
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq870 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq870
  have eq3273 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq3259
  have eq3282 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq3273
       grind)
    | exact superpose eq3273 eq10
    | exact resolve eq10 eq3273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3273
  have eq3312 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3282
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3282
    | exact resolve eq3282 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3282
  have eq3313 : x = (M.op y y) := by grind
  clear eq3312
  have eq3345 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1648 y
       have i₂ := eq3313
       grind)
    | exact superpose eq3313 eq1648
    | exact resolve eq1648 eq3313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648
  have eq3366 : x = (M.op x y) := by
    first
    | (have i₁ := eq1856 y y
       have i₂ := eq3313
       grind)
    | exact superpose eq3313 eq1856
    | exact resolve eq1856 eq3313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1856 eq3313
  have eq3897 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3345
       grind)
    | exact superpose eq3345 eq16
    | exact resolve eq16 eq3345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3345
  have eq3928 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq3897
       have i₂ := eq3366
       grind)
    | exact superpose eq3366 eq3897
    | exact resolve eq3897 eq3366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3366 eq3897
  have eq3929 : False := by grind
  exact eq3929

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = m(X,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pxy_pxx_pxy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op (M.op (M.op X2 X1) (M.op X0 X0)) (M.op (M.op X2 X1) (M.op X0 X0))) = (k (M.op (M.op X2 X1) (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq13 (M.op (M.op X2 X0) (M.op X0 X0)) X0
       have r₂ := eq14 X0 X0 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) := by
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
  clear eq72
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq87
    | exact resolve eq87 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq93
    | exact resolve eq93 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : (M.op y y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq110 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq110 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq110 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq110 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq113 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq111 (σ X0)
       grind)
    | exact superpose eq111 eq10
    | exact resolve eq10 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq111 sF2
       grind)
    | exact superpose eq111 eq49
    | exact resolve eq49 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq117 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq116
       have i₂ := eq111 x
       grind)
    | exact superpose eq111 eq116
    | exact resolve eq116 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq120 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq113 X0
       have i₂ := eq111 X0
       grind)
    | exact superpose eq111 eq113
    | exact resolve eq113 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq113
  have eq560 : ∀ X0 : G, (σ X0) = (M.op y (M.op (M.op x y) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq50 (σ X0)
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq50
    | exact resolve eq50 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq578 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq592 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq50
    | exact resolve eq50 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq594 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq630 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq52 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X1 X1) X1 X2 X1
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq666 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq53 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq52 X0 x x X3
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq677 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq672 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq672
    | exact resolve eq672 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq915 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k (M.op (M.op X2 X1) (M.op X0 X0)) X1) = (M.op (M.op X0 X0) (M.op (M.op X2 X1) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X0 X1 X2
       have i₂ := eq53 (M.op X2 X1) (M.op X0 X0)
       grind)
    | exact superpose eq53 eq65
    | (have j0 := eq65 X0 X1 X2
       grind)
    | (have r₁ := eq65 (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X1 (M.op X0 X1)) X2
       have r₂ := eq53 X0 X1
       grind)
    | (have r₁ := eq65 (M.op X1 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1)) X2
       have r₂ := eq53 X0 X1
       grind)
    | exact resolve eq65 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq1010 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op X1 X1)) X1) = (M.op (M.op X1 X1) (M.op (M.op X0 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq915 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq1928 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq630 X1 (M.op X0 (M.op X0 X0)) X2
       have i₂ := eq630 X0 X0 X0
       grind)
    | exact superpose eq630 eq630
    | exact resolve eq630 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1981 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq630 X0 X0 X0
       grind)
    | exact superpose eq630 eq50
    | exact resolve eq50 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1982 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq630 X0 X0 X0
       grind)
    | exact superpose eq630 eq51
    | exact resolve eq51 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1992 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq578 (M.op x (M.op x x))
       have i₂ := eq630 x x x
       grind)
    | exact superpose eq630 eq578
    | exact resolve eq578 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq1995 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq666 (M.op x (M.op x x)) x
       have i₂ := eq630 x x x
       grind)
    | exact superpose eq630 eq666
    | exact resolve eq666 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq2164 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq587 X0
       have i₂ := eq1981 X0
       grind)
    | exact superpose eq1981 eq587
    | exact resolve eq587 eq1981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2171 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) X0)))) := by
    intro X0
    first
    | (have i₁ := eq592 X0 X0
       have i₂ := eq1981 X0
       grind)
    | exact superpose eq1981 eq592
    | exact resolve eq592 eq1981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq2192 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1981 eq591
    | exact resolve eq591 eq1981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2204 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq591 eq2192
    | exact resolve eq2192 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2192
  have eq2238 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq50 eq2164
    | exact resolve eq2164 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2242 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq560 eq2164
    | exact resolve eq2164 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq2164
  have eq2293 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq2238 X0
       grind)
    | exact superpose eq2238 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq2238 X0
       grind)
    | exact resolve eq13 eq2238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2238
  have eq2313 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2293 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2293
  have eq2362 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2313 (M.op x (M.op x x))
       have i₂ := eq630 x x x
       grind)
    | exact superpose eq630 eq2313
    | exact resolve eq2313 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq2537 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1982 X0
       have i₂ := eq1981 X0
       grind)
    | exact superpose eq1981 eq1982
    | exact resolve eq1982 eq1981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2568 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1982 eq591
    | exact resolve eq591 eq1982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1982
  have eq2580 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq591 eq2568
    | exact resolve eq2568 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591 eq2568
  have eq2808 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1992 (M.op (M.op x sF0) (M.op X0 X0))
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq1992
    | exact resolve eq1992 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1992
  have eq2854 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2808 X0 X1
       have i₂ := eq1981 (M.op (M.op X1 sF0) (M.op X0 X0))
       grind)
    | exact superpose eq1981 eq2808
    | exact resolve eq2808 eq1981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2808
  have eq2869 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2854 X0 x
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq2854
    | exact resolve eq2854 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2854
  have eq3084 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1995 X0 X1
       have i₂ := eq1981 X0
       grind)
    | exact superpose eq1981 eq1995
    | exact resolve eq1995 eq1981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1981 eq1995
  have eq5199 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op y (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq594 X1 X0 X1 X0
       have i₂ := eq677 X0 X1
       grind)
    | exact superpose eq677 eq594
    | exact resolve eq594 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594 eq677
  have eq6887 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq661 (M.op X0 X0) X1 X2
       have i₂ := eq1010 X0 X0
       grind)
    | exact superpose eq1010 eq661
    | exact resolve eq661 eq1010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661 eq1010
  have eq6947 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (k (M.op X0 (M.op X0 X0)) X0)) (k (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6887 X1 X1 X2
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq6887
    | exact resolve eq6887 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6887
  have eq7036 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6947 X0 X1 X2
       have i₂ := eq2362 X0
       grind)
    | exact superpose eq2362 eq6947
    | exact resolve eq6947 eq2362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2362 eq6947
  have eq7187 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7036 X1 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq587 X0
       grind)
    | exact superpose eq587 eq7036
    | exact resolve eq7036 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587 eq7036
  have eq47940 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2869 eq14
    | exact resolve eq14 eq2869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2869
  have eq49772 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op y (M.op y y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1928 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1928
    | (have j0 := eq1928 y x X0
       grind)
    | exact resolve eq1928 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1928
  have eq75127 : y = (M.op (M.op x y) (M.op (M.op y (M.op y x)) (M.op y x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq49772 y
       have i₂ := eq95
       grind)
    | exact superpose eq95 eq49772
    | exact resolve eq49772 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq49772
  have eq75282 : y = (M.op (M.op x y) (M.op (M.op y x) (M.op y x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75127
       have i₂ := eq7187 y (M.op y x)
       grind)
    | exact superpose eq7187 eq75127
    | exact resolve eq75127 eq7187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7187 eq75127
  have eq75318 : y = (M.op (M.op x y) (M.op x (M.op y x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75282
       have i₂ := eq53 y x
       grind)
    | exact superpose eq53 eq75282
    | exact resolve eq75282 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq75282
  have eq75337 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq47940 eq75318
    | exact resolve eq75318 eq47940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47940 eq75318
  have eq75366 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq75337 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq75337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75367 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq75366
    | exact resolve eq75366 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75366
  have eq75378 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq75367
       have r₂ := eq27
       grind)
    | exact resolve eq75367 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75367
  have eq75382 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq75378
    | exact resolve eq75378 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75378
  have eq75410 : (σ y) = (M.op y (M.op (M.op x y) (M.op (σ y) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq75382 eq50
    | exact resolve eq50 eq75382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75382
  have eq75815 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq75410 eq5199
    | exact resolve eq5199 eq75410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5199
  have eq75920 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq75815
    | exact resolve eq75815 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75815
  have eq75960 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq75920 eq3084
    | exact resolve eq3084 eq75920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3084 eq75920
  have eq84548 : (M.op (σ y) (σ x)) = (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (σ x))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq75960 eq2537
    | exact resolve eq2537 eq75960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2537 eq75960
  have eq84653 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2171 eq84548
    | exact resolve eq84548 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2171 eq84548
  have eq84674 : (σ y) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq84653 eq75410
    | exact resolve eq75410 eq84653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75410 eq84653
  have eq84749 : (σ y) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq84674
  have eq84755 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq50 eq84749
    | exact resolve eq84749 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq84749
  have eq84757 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq84755 eq27
    | exact resolve eq27 eq84755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84811 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq84755 eq2580
    | exact resolve eq2580 eq84755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2580
  have eq84863 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq84811
    | exact resolve eq84811 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84811
  have eq85310 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq84863 eq2313
    | exact resolve eq2313 eq84863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2313 eq84863
  have eq85656 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq84755 eq85310
    | exact resolve eq85310 eq84755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84755 eq85310
  have eq85674 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq85656
  have eq85691 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq85674 eq75337
    | exact resolve eq75337 eq85674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75337 eq85674
  have eq85701 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq85691
  have eq85706 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq85701
       have r₂ := eq84757
       grind)
    | exact resolve eq85701 eq84757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84757 eq85701
  have eq85721 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq85706 eq29
    | exact resolve eq29 eq85706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq85706
  have eq85994 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq85721
    | exact resolve eq85721 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq85721
  have eq85995 : x = (M.op x y) ∨ x = y := by grind
  clear eq85994
  have eq86030 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq85995 eq20
    | exact resolve eq20 eq85995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86146 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq85995 eq2204
    | exact resolve eq2204 eq85995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2204 eq85995
  have eq86244 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq86146
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq86146
    | exact resolve eq86146 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86146
  have eq86310 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq86030
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq86030
    | exact resolve eq86030 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86030
  have eq86349 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq86310 eq26
    | exact resolve eq26 eq86310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86310
  have eq86691 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2242 y
       have i₂ := eq86244
       grind)
    | exact superpose eq86244 eq2242
    | exact resolve eq2242 eq86244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2242 eq86244
  have eq86822 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq86691
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq86691
    | exact resolve eq86691 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86691
  have eq86897 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq86822
    | exact resolve eq86822 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86822
  have eq89204 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq86897 eq86349
    | exact resolve eq86349 eq86897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86349 eq86897
  have eq89268 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq89204
  have eq89289 : x = y := by
    first
    | (have r₁ := eq89268
       have r₂ := eq27
       grind)
    | exact resolve eq89268 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89268
  have eq89300 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq89289
       grind)
    | exact superpose eq89289 eq18
    | exact resolve eq18 eq89289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq89301 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq89289
       grind)
    | exact superpose eq89289 eq24
    | exact resolve eq24 eq89289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq89289
  have eq89581 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq89301
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq89301
    | exact resolve eq89301 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq89301
  have eq89639 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq89581 eq26
    | exact resolve eq26 eq89581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq89581
  have eq90475 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq89639 eq117
    | exact resolve eq117 eq89639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq89639
  have eq90773 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq90475
       have i₂ := eq89300
       grind)
    | exact superpose eq89300 eq90475
    | exact resolve eq90475 eq89300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89300 eq90475
  have eq90921 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq90773 eq15
    | exact resolve eq15 eq90773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90773
  have eq91037 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq90921
    | exact resolve eq90921 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq90921
  have eq91080 : False := by grind
  exact eq91080

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pxx_pyy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
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
  clear eq18
  have eq33 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X1)) (M.op (M.op X0 X1) (M.op X1 X1))) = (k (M.op (M.op X0 X1) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq12 (M.op (M.op X0 X1) (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq12 (M.op (M.op x X0) (M.op X0 X0)) X0
       have r₂ := eq9 X0 X0 x
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op (M.op (M.op X2 X1) (M.op X0 X0)) (M.op (M.op X2 X1) (M.op X0 X0))) = (k (M.op (M.op X2 X1) (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq12 (M.op (M.op X2 X0) (M.op X0 X0)) X0
       have r₂ := eq9 X0 X0 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k (M.op (M.op X2 X1) (M.op X0 X0)) X1) = (M.op (M.op X0 X0) (M.op (M.op X2 X1) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 X1 X2
       have i₂ := eq24 (M.op X2 X1) (M.op X0 X0)
       grind)
    | exact superpose eq24 eq34
    | (have j0 := eq34 X0 X1 X2
       grind)
    | (have r₁ := eq34 (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X1 (M.op X0 X1)) X2
       have r₂ := eq24 X0 X1
       grind)
    | (have r₁ := eq34 (M.op X1 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1)) X2
       have r₂ := eq24 X0 X1
       grind)
    | exact resolve eq34 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq36 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op X1 X1)) X1) = (M.op (M.op X1 X1) (M.op (M.op X0 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq24 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact superpose eq24 eq33
    | exact resolve eq33 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq37 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq46 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq46 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq46 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq49 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq47 (σ X0)
       grind)
    | exact superpose eq47 eq15
    | exact resolve eq15 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq49 X0
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq49
    | exact resolve eq49 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq49
  have eq64 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq68 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq85 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       have j1 := eq78 X0 X1
       grind)
    | (have r₁ := eq81 X0 X1
       have r₂ := eq78 X0 X1
       grind)
    | (have r₁ := eq81 X0 X0
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq81 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq81
  have eq87 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X1
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq64
    | (have j0 := eq64 X0 X1
       grind)
    | exact resolve eq64 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq111 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq111 X0
       grind)
    | exact superpose eq111 eq12
    | (have j0 := eq12 (M.op X0 (M.op X0 X0)) X0
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op X0 X0)) X0
       have r₂ := eq111 X0
       grind)
    | exact resolve eq12 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq111 X0
       grind)
    | exact superpose eq111 eq9
    | exact resolve eq9 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have j0 := eq127 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq130 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq129 X0
       have i₂ := eq24 X0 (M.op X0 X0)
       grind)
    | exact superpose eq24 eq129
    | exact resolve eq129 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq140 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 (M.op X1 X0))) (M.op (M.op X1 X0) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23 (M.op X1 X0) X2 X3 X4
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq23
    | exact resolve eq23 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3 X4
       have i₂ := eq23 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq23
    | exact resolve eq23 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23 X4 X2 X3 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq23 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (M.op X1 X1) X1 X2 X1
       have i₂ := eq24 X1 X1
       grind)
    | exact superpose eq24 eq23
    | exact resolve eq23 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq23 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq23 eq24
    | exact resolve eq24 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq24 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq23 X0 x x X3
       grind)
    | exact superpose eq23 eq24
    | exact resolve eq24 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq9 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq23 X1 x x X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq23 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq169 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq168 X0 X1 X2 X3
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq168
    | exact resolve eq168 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq176 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq159 X0 X1
       have i₂ := eq130 (M.op X0 X1)
       grind)
    | exact superpose eq130 eq159
    | exact resolve eq159 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq159
  have eq181 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq149 X0 X1 X2 X3 X4
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq149
    | exact resolve eq149 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq183 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq141 X0 X1 X2 X3 X4
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq141
    | exact resolve eq141 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq189 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 X1
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq176
    | exact resolve eq176 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq207 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq9
    | exact resolve eq9 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq85
    | (have j0 := eq85 (σ X1) (σ X0)
       grind)
    | exact resolve eq85 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq85 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq314 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq311 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq311 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq311 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq311 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq328 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq275 X0 X1
       have i₂ := eq56 X1
       grind)
    | exact superpose eq56 eq275
    | (have j0 := eq275 X0 X1
       grind)
    | exact resolve eq275 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq412 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 (M.op X0 (M.op X1 X0))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq160 (M.op X0 X1) x
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq160
    | exact resolve eq160 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       have i₂ := eq160 (M.op X0 X0) x
       grind)
    | exact superpose eq160 eq9
    | exact resolve eq9 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq425 X0
       have i₂ := eq24 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq24 eq425
    | exact resolve eq425 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq437 : ∀ X0 : G, (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq433 X0
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq433
    | exact resolve eq433 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq438 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq437 X0
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq437
    | exact resolve eq437 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq455 : ∀ X0 : G, (M.op X0 X0) = (k (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq438 (M.op X0 X0)
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq438
    | exact resolve eq438 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470 : ∀ X0 : G, (M.op X0 X0) = (k (k (M.op X0 (M.op X0 X0)) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq455 X0
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq455
    | exact resolve eq455 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq476 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq470 X0
       have i₂ := eq438 X0
       grind)
    | exact superpose eq438 eq470
    | exact resolve eq470 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470
  have eq698 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq476 X0
       have i₂ := eq314 X0 (M.op X0 X0)
       grind)
    | exact superpose eq314 eq476
    | (have j1 := eq314 X0 (M.op X0 X0)
       grind)
    | exact resolve eq476 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq702 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq314 (σ X1) (σ X0)
       grind)
    | exact superpose eq314 eq15
    | (have j1 := eq314 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq704 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq314 (τ X1) X0
       grind)
    | exact superpose eq314 eq17
    | (have j1 := eq314 (τ X1) X0
       grind)
    | exact resolve eq17 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq707 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq698 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq841 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq707 (σ X0)
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq707
    | exact resolve eq707 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq914 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq87 x y
       grind)
    | exact superpose eq87 eq16
    | (have j1 := eq87 x y
       grind)
    | exact resolve eq16 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq1834 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq164 X0 X0 X0
       grind)
    | exact superpose eq164 eq9
    | exact resolve eq9 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1853 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq160 (M.op x (M.op x x)) x
       have i₂ := eq164 x x x
       grind)
    | exact superpose eq164 eq160
    | exact resolve eq160 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2939 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq117 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq117 eq117
    | exact resolve eq117 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3242 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq153 (M.op X0 X0) X1 X2
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq153
    | exact resolve eq153 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq3273 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (k (M.op X0 (M.op X0 X0)) X0)) (k (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3242 X1 X1 X2
       have i₂ := eq24 X1 X1
       grind)
    | exact superpose eq24 eq3242
    | exact resolve eq3242 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3242
  have eq3286 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3273 X0 X1 X2
       have i₂ := eq438 X0
       grind)
    | exact superpose eq438 eq3273
    | exact resolve eq3273 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438 eq3273
  have eq3330 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3286 X1 (σ x) (M.op (σ (M.op x x)) (M.op X0 X0))
       have i₂ := eq207 x X0
       grind)
    | exact superpose eq207 eq3286
    | exact resolve eq3286 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq3286
  have eq3466 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) = (k (M.op (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) (M.op X0 X1)) (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq189 (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))
       have i₂ := eq117 X1 X0 (M.op X1 (M.op X0 X1)) X2
       grind)
    | exact superpose eq117 eq189
    | exact resolve eq189 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq3562 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) = (k (M.op (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) (M.op X0 X1)) (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3466 X0 X1 X0
       have i₂ := eq3330 X0 (M.op X1 (M.op X0 X1))
       grind)
    | exact superpose eq3330 eq3466
    | exact resolve eq3466 eq3330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3466
  have eq3579 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (k (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3562 X0 X0
       have i₂ := eq24 X0 (M.op X0 X0)
       grind)
    | exact superpose eq24 eq3562
    | exact resolve eq3562 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3562
  have eq3593 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X1))) = (k (M.op (M.op X1 (M.op X1 (M.op X0 X1))) (M.op X0 X1)) (M.op X1 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3579 X1 X0
       have i₂ := eq2939 X0 X1 X0
       grind)
    | exact superpose eq2939 eq3579
    | exact resolve eq3579 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3579
  have eq3598 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X1))) = (k (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3593 X0 X1
       have i₂ := eq412 X1 X0 X1
       grind)
    | exact superpose eq412 eq3593
    | exact resolve eq3593 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3593
  have eq4617 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op (M.op X2 X3) (M.op X1 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq148 (M.op X0 X1) X1 X2 X3 X1
       have i₂ := eq117 X1 X0 X1 X0
       grind)
    | exact superpose eq117 eq148
    | exact resolve eq148 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5154 : ∀ X0 X1 X2 X3 X6 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op (M.op X6 (M.op X1 (M.op X0 X1))) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X6
    first
    | (have i₁ := eq169 (M.op (M.op X2 X3) (M.op x x)) (M.op x (M.op X0 (M.op X1 X0))) X2 X3
       have i₂ := eq148 X0 X1 X2 X3 x
       grind)
    | exact superpose eq148 eq169
    | exact resolve eq169 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5340 : ∀ X0 X1 X2 X3 X6 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op X1 (M.op (M.op X6 (M.op X1 (M.op X0 X1))) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X6
    first
    | (have i₁ := eq5154 X0 X1 X2 X3 X6
       have i₂ := eq2939 (M.op X6 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq2939 eq5154
    | exact resolve eq5154 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5154
  have eq5425 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op X1 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5340 X0 X1 X2 X3 x
       have i₂ := eq412 X1 X0 x
       grind)
    | exact superpose eq412 eq5340
    | exact resolve eq5340 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq5340
  have eq5572 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq111 X2
       have i₂ := eq1834 X2 X0 X1
       grind)
    | exact superpose eq1834 eq111
    | exact resolve eq111 eq1834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq5580 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1853 X2 X3
       have i₂ := eq1834 X2 X0 X1
       grind)
    | exact superpose eq1834 eq1853
    | exact resolve eq1853 eq1834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5686 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = (M.op (M.op (M.op X3 (M.op X2 X1)) X0) (M.op X0 (M.op (M.op X3 (M.op X2 X1)) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq169 (M.op X3 (M.op X2 X1)) X0 X1 X2
       have i₂ := eq1834 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq1834 eq169
    | exact resolve eq169 eq1834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq5695 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op (M.op X3 (M.op X2 X1)) X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5686 X0 X1 X2 X3
       have i₂ := eq2939 X0 (M.op X3 (M.op X2 X1)) X0
       grind)
    | exact superpose eq2939 eq5686
    | exact resolve eq5686 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5686
  have eq6114 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 X0)) = (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op (M.op X2 (M.op X1 X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5572 (M.op X2 (M.op X1 X2)) (M.op x x) (M.op (M.op X1 X2) (M.op X0 X0))
       have i₂ := eq140 X2 X1 x x X0
       grind)
    | exact superpose eq140 eq5572
    | exact resolve eq5572 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6123 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) = (M.op (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5572 X3 X2 (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0))
       have i₂ := eq9 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq9 eq5572
    | exact resolve eq5572 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6142 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) X0) = (M.op (M.op (M.op X1 (M.op X2 X0)) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5572 X0 X2 (M.op (M.op X1 (M.op X2 X0)) X0)
       have i₂ := eq5572 (M.op X2 X0) X1 X0
       grind)
    | exact superpose eq5572 eq5572
    | exact resolve eq5572 eq5572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6205 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6142 X0 X1 X2
       have i₂ := eq3330 (M.op X1 (M.op X2 X0)) X0
       grind)
    | exact superpose eq3330 eq6142
    | exact resolve eq6142 eq3330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6142
  have eq6209 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) = (M.op X0 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6123 X0 X1 X2 X3
       have i₂ := eq4617 X3 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq4617 eq6123
    | exact resolve eq6123 eq4617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6123
  have eq6211 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 X0)) = (M.op X0 (M.op (M.op X2 (M.op X1 X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6114 X0 X1 X2
       have i₂ := eq4617 (M.op X2 (M.op X1 X2)) X0 X1 X2
       grind)
    | exact superpose eq4617 eq6114
    | exact resolve eq6114 eq4617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4617 eq6114
  have eq6878 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op (M.op X1 X2) (M.op X0 X0))) = (M.op (M.op X3 X0) (M.op (M.op X1 X2) (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6205 (M.op (M.op X1 X2) (M.op X0 X0)) X3 (M.op (M.op x x) (M.op X2 (M.op X1 X2)))
       have i₂ := eq140 X2 X1 x x X0
       grind)
    | exact superpose eq140 eq6205
    | exact resolve eq6205 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq7022 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X2) (M.op X0 X0))) = (M.op (M.op X3 X0) (M.op (M.op X1 X2) (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6878 X0 X1 X2 X3
       have i₂ := eq24 (M.op X1 X2) (M.op X0 X0)
       grind)
    | exact superpose eq24 eq6878
    | exact resolve eq6878 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6878
  have eq7058 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X0))) = (M.op (M.op X3 X0) (M.op (M.op X1 X2) (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7022 X0 X1 X2 X3
       have i₂ := eq2939 (M.op X1 X2) X0 X0
       grind)
    | exact superpose eq2939 eq7022
    | exact resolve eq7022 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7022
  have eq7497 : ∀ X0 X1 X2 X3 X4 X5 : G, (k (M.op (M.op X0 (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2)))) (M.op (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))))) (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2)))) = (M.op (M.op (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2)))) (M.op (M.op X0 (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2)))) (M.op (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have j0 := eq35 (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2))) X0
       grind)
    | (have r₁ := eq35 (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) X2
       have r₂ := eq181 X0 X1 X2 X3 X4
       grind)
    | (have r₁ := eq35 (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) X2
       have r₂ := eq181 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq35 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq7766 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X4 (M.op X3 X4)) = (M.op X5 (M.op (M.op X6 X5) (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X2 (M.op X3 X4))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq117 (M.op X3 X4) X4 X5 X6
       have i₂ := eq181 X3 X4 X0 X1 X2
       grind)
    | exact superpose eq181 eq117
    | exact resolve eq117 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq8097 : ∀ X0 X1 X2 X3 X4 X5 : G, (k (M.op (M.op X0 (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2)))) (M.op (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))))) (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2)))) = (M.op (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) (M.op (M.op X0 (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2)))) (M.op (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq7497 X0 X1 X2 X3 X4 X5
       have i₂ := eq7058 (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) X0 (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2))) (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2)))
       grind)
    | exact superpose eq7058 eq7497
    | exact resolve eq7497 eq7058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7058 eq7497
  have eq8192 : ∀ X1 X2 X3 X4 X5 : G, (k (M.op (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) (M.op (M.op X2 (M.op X1 X2)) (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))))) (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2)))) = (M.op (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) (M.op (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) (M.op (M.op X2 (M.op X1 X2)) (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2)))))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq8097 X1 X1 X2 X3 X4 X5
       have i₂ := eq6209 (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) X1 (M.op X1 X2) (M.op X2 (M.op X1 X2))
       grind)
    | exact superpose eq6209 eq8097
    | exact resolve eq8097 eq6209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8097
  have eq8251 : ∀ X1 X2 X3 X4 X5 : G, (k (M.op (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) (M.op (M.op X2 (M.op X1 X2)) (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))))) (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2)))) = (M.op X2 (M.op (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) (M.op (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2)))))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq8192 X1 X2 X3 X4 X5
       have i₂ := eq5695 (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) X2 X1 X2
       grind)
    | exact superpose eq5695 eq8192
    | exact resolve eq8192 eq5695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8192
  have eq8276 : ∀ X1 X2 X3 X4 X5 : G, (k (M.op (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) (M.op (M.op X2 (M.op X1 X2)) (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))))) (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2)))) = (M.op X2 (M.op (M.op X5 (M.op X1 X2)) (M.op (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2)))))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq8251 X1 X2 X3 X4 X5
       have i₂ := eq2939 (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))
       grind)
    | exact superpose eq2939 eq8251
    | exact resolve eq8251 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8251
  have eq8288 : ∀ X1 X2 X3 X4 X5 : G, (k (M.op (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) (M.op (M.op X2 (M.op X1 X2)) (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))))) (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2)))) = (M.op X2 (M.op (M.op X5 (M.op X1 X2)) (M.op (M.op X5 (M.op X1 X2)) (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2)))))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq8276 X1 X2 X3 X4 X5
       have i₂ := eq5425 (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2)) (M.op X5 (M.op X1 X2)) (M.op (M.op X3 X4) (M.op X5 X5))
       grind)
    | exact superpose eq5425 eq8276
    | exact resolve eq8276 eq5425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8276
  have eq8292 : ∀ X1 X2 X3 X4 X5 : G, (k (M.op (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) (M.op (M.op X2 (M.op X1 X2)) (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))))) (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2)))) = (M.op X2 (M.op X5 (M.op (M.op X5 (M.op X1 X2)) (M.op (M.op X5 (M.op X1 X2)) (M.op X5 (M.op X1 X2)))))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq8288 X1 X2 X3 X4 X5
       have i₂ := eq5695 (M.op X5 (M.op X1 X2)) X5 X5 (M.op X3 X4)
       grind)
    | exact superpose eq5695 eq8288
    | exact resolve eq8288 eq5695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5695 eq8288
  have eq8295 : ∀ X1 X2 X3 X4 X5 : G, (k (M.op (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) (M.op (M.op X2 (M.op X1 X2)) (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))))) (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2)))) = (M.op X2 (M.op X5 (M.op (M.op X1 X2) (M.op (M.op X5 (M.op X1 X2)) (M.op X5 (M.op X1 X2)))))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq8292 X1 X2 X3 X4 X5
       have i₂ := eq2939 (M.op X5 (M.op X1 X2)) X5 (M.op X1 X2)
       grind)
    | exact superpose eq2939 eq8292
    | exact resolve eq8292 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8292
  have eq8298 : ∀ X1 X2 X3 X4 X5 : G, (k (M.op (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) (M.op (M.op X2 (M.op X1 X2)) (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))))) (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2)))) = (M.op X2 (M.op X5 (M.op (M.op X1 X2) (M.op (M.op X1 X2) (M.op X5 (M.op X1 X2)))))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq8295 X1 X2 X3 X4 X5
       have i₂ := eq5425 X5 (M.op X1 X2) (M.op X1 X2) X5
       grind)
    | exact superpose eq5425 eq8295
    | exact resolve eq8295 eq5425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8295
  have eq8301 : ∀ X1 X2 X3 X4 X5 : G, (k (M.op (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) (M.op (M.op X2 (M.op X1 X2)) (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))))) (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2)))) = (M.op X2 (M.op X5 (M.op (M.op X1 X2) (M.op X2 (M.op X5 (M.op X1 X2)))))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq8298 X1 X2 X3 X4 X5
       have i₂ := eq2939 X5 X1 X2
       grind)
    | exact superpose eq2939 eq8298
    | exact resolve eq8298 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8298
  have eq8303 : ∀ X1 X2 X3 X4 X5 : G, (M.op X2 (M.op X5 (M.op (M.op X1 X2) (M.op X2 (M.op X5 (M.op X1 X2)))))) = (k (M.op (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) (M.op (M.op X2 (M.op X1 X2)) (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))))) (M.op X2 (M.op X2 (M.op X1 X2)))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq8301 X1 X2 X3 X4 X5
       have i₂ := eq2939 X2 X1 X2
       grind)
    | exact superpose eq2939 eq8301
    | exact resolve eq8301 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8301
  have eq8304 : ∀ X1 X2 X3 X4 X5 : G, (M.op X2 (M.op X5 (M.op (M.op X1 X2) (M.op X2 (M.op X5 (M.op X1 X2)))))) = (k (M.op (M.op X1 X2) (M.op (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))))) (M.op X2 (M.op X2 (M.op X1 X2)))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq8303 X1 X2 X3 X4 X5
       have i₂ := eq6211 (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))) X1 X2
       grind)
    | exact superpose eq6211 eq8303
    | exact resolve eq8303 eq6211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6211 eq8303
  have eq8305 : ∀ X1 X2 X3 X4 X5 : G, (M.op X2 (M.op X5 (M.op (M.op X1 X2) (M.op X2 (M.op X5 (M.op X1 X2)))))) = (k (M.op (M.op X1 X2) (M.op (M.op X5 (M.op X1 X2)) (M.op (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))))) (M.op X2 (M.op X2 (M.op X1 X2)))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq8304 X1 X2 X3 X4 X5
       have i₂ := eq24 (M.op (M.op X3 X4) (M.op X5 X5)) (M.op X5 (M.op X1 X2))
       grind)
    | exact superpose eq24 eq8304
    | exact resolve eq8304 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8304
  have eq8306 : ∀ X1 X2 X5 : G, (M.op X2 (M.op X5 (M.op (M.op X1 X2) (M.op X2 (M.op X5 (M.op X1 X2)))))) = (k (M.op X2 (M.op X1 X2)) (M.op X2 (M.op X2 (M.op X1 X2)))) := by
    intro X1 X2 X5
    first
    | (have i₁ := eq8305 X1 X2 x x X5
       have i₂ := eq7766 x x X5 X1 X2 (M.op X1 X2) X5
       grind)
    | exact superpose eq7766 eq8305
    | exact resolve eq8305 eq7766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7766 eq8305
  have eq8307 : ∀ X1 X2 X5 : G, (M.op X2 (M.op X2 (M.op X1 X2))) = (M.op X2 (M.op X5 (M.op (M.op X1 X2) (M.op X2 (M.op X5 (M.op X1 X2)))))) := by
    intro X1 X2 X5
    first
    | (have i₁ := eq8306 X1 X2 X5
       have i₂ := eq3598 X1 X2
       grind)
    | exact superpose eq3598 eq8306
    | exact resolve eq8306 eq3598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3598 eq8306
  have eq8749 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op X0 X0)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq164 (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op X0 X0)) X1 X2
       have i₂ := eq183 X0 X0 (M.op X0 X0) (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq183 eq164
    | exact resolve eq164 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq183
  have eq8863 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 (M.op X0 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8749 X0 X1 X2
       have i₂ := eq6209 X2 (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) X0 X0
       grind)
    | exact superpose eq6209 eq8749
    | exact resolve eq8749 eq6209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8749
  have eq9174 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) X0) = (M.op (M.op X1 X2) (M.op (M.op (M.op X3 X2) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8863 X2 X1 (M.op (M.op X3 X2) X0)
       have i₂ := eq1834 X0 X2 X3
       grind)
    | exact superpose eq1834 eq8863
    | exact resolve eq8863 eq1834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1834
  have eq9203 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 (M.op X2 X2))) (M.op (M.op X2 (M.op X0 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8863 (M.op X2 (M.op X2 X2)) X1 (M.op X2 (M.op X0 X0))
       have i₂ := eq128 X2 X0
       grind)
    | exact superpose eq128 eq8863
    | exact resolve eq8863 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq9279 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op (M.op X4 X1) (M.op X4 X1))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq148 X0 X1 X2 X3 (M.op X4 X1)
       have i₂ := eq8863 X1 X4 X0
       grind)
    | exact superpose eq8863 eq148
    | exact resolve eq148 eq8863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq9333 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = (M.op (M.op X2 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6205 (M.op X0 (M.op X1 X0)) X2 (M.op x X1)
       have i₂ := eq8863 X1 x X0
       grind)
    | exact superpose eq8863 eq6205
    | exact resolve eq6205 eq8863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9334 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (M.op (M.op X2 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9333 X0 X1 X2
       have i₂ := eq24 X0 (M.op X1 X0)
       grind)
    | exact superpose eq24 eq9333
    | exact resolve eq9333 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9333
  have eq9358 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X1 (M.op X4 X1))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9279 X0 X1 X2 X3 X4
       have i₂ := eq24 X4 X1
       grind)
    | exact superpose eq24 eq9279
    | exact resolve eq9279 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9279
  have eq9387 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 (M.op X2 X2))) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9203 X0 X1 X2
       have i₂ := eq160 X0 X2
       grind)
    | exact superpose eq160 eq9203
    | exact resolve eq9203 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq9203
  have eq9402 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X3 X2) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9174 X0 X3 X2 X1
       have i₂ := eq1853 X0 (M.op X1 X2)
       grind)
    | exact superpose eq1853 eq9174
    | exact resolve eq9174 eq1853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853 eq9174
  have eq9414 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = (M.op (M.op X2 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9334 X0 X1 X2
       have i₂ := eq2939 X0 X1 X0
       grind)
    | exact superpose eq2939 eq9334
    | exact resolve eq9334 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9334
  have eq9429 : ∀ X0 X2 : G, (M.op X2 (M.op X0 X0)) = (M.op X0 (M.op (M.op X2 X2) X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq9387 X0 x X2
       have i₂ := eq6209 X0 x X2 (M.op X2 X2)
       grind)
    | exact superpose eq6209 eq9387
    | exact resolve eq9387 eq6209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6209 eq9387
  have eq9731 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X1 (M.op X0 (M.op X2 X0))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9402 X3 X1 (M.op X0 (M.op X2 X0)) (M.op x X2)
       have i₂ := eq8863 X2 x X0
       grind)
    | exact superpose eq8863 eq9402
    | exact resolve eq9402 eq8863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9737 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) X4) = (M.op (M.op X2 (M.op X3 (M.op X0 X1))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9402 X4 X2 (M.op X3 (M.op X0 X1)) (M.op (M.op x x) (M.op X3 X3))
       have i₂ := eq181 X0 X1 x x X3
       grind)
    | exact superpose eq181 eq9402
    | exact resolve eq9402 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10041 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X2 X1
       have i₂ := eq9402 (M.op X2 X1) X2 X1 X0
       grind)
    | (have i₁ := eq24 X2 X1
       have i₂ := eq9402 (M.op X2 X1) X0 X1 X2
       grind)
    | exact superpose eq9402 eq24
    | exact resolve eq24 eq9402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10341 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X4) = (M.op (M.op X2 (M.op X3 (M.op X0 X1))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9737 X0 X1 X2 X3 X4
       have i₂ := eq9358 X4 X1 X0 X1 X0
       grind)
    | exact superpose eq9358 eq9737
    | exact resolve eq9737 eq9358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9358 eq9737
  have eq13623 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5580 (M.op X0 (M.op X0 X0)) (M.op (M.op x x) (M.op X0 (M.op X0 X0))) X2 X1
       have i₂ := eq153 X0 x x
       grind)
    | exact superpose eq153 eq5580
    | exact resolve eq5580 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq5580
  have eq16897 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9429 (M.op X0 (M.op X1 X0)) X1
       have i₂ := eq8863 X1 X1 X0
       grind)
    | exact superpose eq8863 eq9429
    | exact resolve eq9429 eq8863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8863 eq9429
  have eq17250 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq16897 X0 X1
       have i₂ := eq24 X0 (M.op X1 X0)
       grind)
    | exact superpose eq24 eq16897
    | exact resolve eq16897 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16897
  have eq17306 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17250 X0 X1
       have i₂ := eq9414 X0 X1 X1
       grind)
    | exact superpose eq9414 eq17250
    | exact resolve eq17250 eq9414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17250
  have eq17330 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17306 X0 X1
       have i₂ := eq6205 X0 X0 X1
       grind)
    | exact superpose eq6205 eq17306
    | exact resolve eq17306 eq6205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6205 eq17306
  have eq24479 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq328 y x
       grind)
    | exact superpose eq328 eq16
    | (have j1 := eq328 y x
       grind)
    | exact resolve eq16 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq25685 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq914
       have i₂ := eq314 y x
       grind)
    | exact superpose eq314 eq914
    | (have j1 := eq314 (σ y) (σ x)
       grind)
    | exact resolve eq914 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq25690 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq25685
  have eq26616 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X0 X1)) (M.op X3 (M.op X2 (M.op X0 X1)))) = (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (M.op X3 (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10041 (M.op (M.op x x) (M.op X2 X2)) (M.op X2 (M.op X0 X1)) X3
       have i₂ := eq181 X0 X1 x x X2
       grind)
    | exact superpose eq181 eq10041
    | exact resolve eq10041 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq10041
  have eq27156 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X0 X1)) (M.op X3 (M.op X2 (M.op X0 X1)))) = (M.op X1 (M.op X3 (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq26616 X0 X1 X2 X3
       have i₂ := eq9731 X1 (M.op X0 X1) X0 (M.op X3 (M.op X2 (M.op X0 X1)))
       grind)
    | exact superpose eq9731 eq26616
    | exact resolve eq26616 eq9731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9731 eq26616
  have eq27218 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X3 (M.op X2 (M.op X0 X1)))) = (M.op (M.op X0 X1) (M.op X3 (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq27156 X0 X1 X2 X3
       have i₂ := eq2939 X3 X2 (M.op X0 X1)
       grind)
    | exact superpose eq2939 eq27156
    | exact resolve eq27156 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27156
  have eq31615 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op X2 X1)) = (M.op X3 (M.op (M.op X0 X1) (M.op (M.op X2 X1) (M.op X3 (M.op X2 X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17330 (M.op X2 X1) X3
       have i₂ := eq9402 (M.op (M.op X2 X1) (M.op X3 (M.op X2 X1))) X2 X1 X0
       grind)
    | (have i₁ := eq17330 (M.op X2 X1) X3
       have i₂ := eq9402 (M.op (M.op X2 X1) (M.op X3 (M.op X2 X1))) X0 X1 X2
       grind)
    | exact superpose eq9402 eq17330
    | exact resolve eq17330 eq9402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9402
  have eq31868 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op X2 X1)) = (M.op X3 (M.op (M.op X0 X1) (M.op X1 (M.op X3 (M.op X2 X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq31615 X0 X1 X2 X3
       have i₂ := eq2939 X3 X2 X1
       grind)
    | exact superpose eq2939 eq31615
    | exact resolve eq31615 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31615
  have eq31988 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X1)) = (M.op X3 (M.op (M.op X0 X1) (M.op X1 (M.op X3 (M.op X2 X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq31868 X0 X1 X2 X3
       have i₂ := eq24 X2 X1
       grind)
    | exact superpose eq24 eq31868
    | exact resolve eq31868 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31868
  have eq121391 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq704 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq704
    | exact resolve eq704 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq121617 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq121391 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq121391
    | (have j0 := eq121391 X0 X1
       grind)
    | exact resolve eq121391 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121391
  have eq150165 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2))))) = (M.op X2 (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq10341 X1 X2 X4 X0 (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2))))
       have i₂ := eq2939 X3 X4 (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq2939 eq10341
    | exact resolve eq10341 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10341
  have eq150550 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2))))) = (M.op (M.op X1 X2) (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq150165 X0 X1 X2 X3 X4
       have i₂ := eq27218 X0 (M.op X1 X2) X4 X3
       grind)
    | exact superpose eq27218 eq150165
    | exact resolve eq150165 eq27218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150165
  have eq167390 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17330 X3 X2
       have i₂ := eq5425 X2 X3 X0 X1
       grind)
    | exact superpose eq5425 eq17330
    | exact resolve eq17330 eq5425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5425 eq17330
  have eq191763 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq702 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq192370 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq191763 (τ X1) (τ X0)
       have i₂ := eq37 X1 X0
       grind)
    | exact superpose eq37 eq191763
    | (have j0 := eq191763 (τ X1) (τ X0)
       grind)
    | exact resolve eq191763 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq191763
  have eq192419 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq192370 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq192370
    | (have j0 := eq192370 X0 X1
       grind)
    | exact resolve eq192370 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192370
  have eq192441 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq192419 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq192419
    | (have j0 := eq192419 X0 X1
       grind)
    | exact resolve eq192419 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192419
  have eq192452 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq192441 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq192441
    | (have j0 := eq192441 X0 X1
       grind)
    | exact resolve eq192441 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192441
  have eq192462 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq192452 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq192452
    | (have j0 := eq192452 X0 X1
       grind)
    | exact resolve eq192452 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192452
  have eq555111 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X0))) ≠ X0 ∨ (k (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X1 X0))))) X0) = (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X1 X0))))) (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X1 X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X1 X0))))) X0
       have i₂ := eq8307 X1 X0 X2
       grind)
    | exact superpose eq8307 eq12
    | (have j0 := eq12 (M.op X0 (M.op X1 X0)) X0
       grind)
    | exact resolve eq12 eq8307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8307
  have eq556010 : ∀ X0 X1 X2 : G, (k (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X1 X0))))) X0) = (M.op (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X1 X0)))) (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X1 X0)))))) ∨ (M.op X0 (M.op X0 (M.op X1 X0))) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq555111 X0 X1 X2
       have i₂ := eq24 X2 (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X1 X0))))
       grind)
    | exact superpose eq24 eq555111
    | (have j0 := eq555111 X0 X1 X2
       grind)
    | exact resolve eq555111 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq555111
  have eq556988 : ∀ X0 X1 X2 : G, (k (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X1 X0))))) X0) = (M.op (M.op X0 (M.op X2 (M.op X1 X0))) (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X1 X0)))))) ∨ (M.op X0 (M.op X0 (M.op X1 X0))) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq556010 X0 X1 X2
       have i₂ := eq2939 X2 (M.op X1 X0) (M.op X0 (M.op X2 (M.op X1 X0)))
       grind)
    | exact superpose eq2939 eq556010
    | (have j0 := eq556010 X0 X1 X2
       grind)
    | exact resolve eq556010 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2939 eq556010
  have eq557726 : ∀ X0 X1 X2 : G, (k (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X1 X0))))) X0) = (M.op (M.op X2 (M.op X1 X0)) (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X1 X0)))))) ∨ (M.op X0 (M.op X0 (M.op X1 X0))) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq556988 X0 X1 X2
       have i₂ := eq27218 X0 (M.op X2 (M.op X1 X0)) (M.op X1 X0) X2
       grind)
    | exact superpose eq27218 eq556988
    | (have j0 := eq556988 X0 X1 X2
       grind)
    | exact resolve eq556988 eq27218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27218 eq556988
  have eq558307 : ∀ X0 X1 X2 : G, (k (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X1 X0))))) X0) = (M.op (M.op X1 X0) (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X1 X0)))))) ∨ (M.op X0 (M.op X0 (M.op X1 X0))) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq557726 X0 X1 X2
       have i₂ := eq150550 X0 X2 (M.op X1 X0) X2 (M.op X1 X0)
       grind)
    | exact superpose eq150550 eq557726
    | (have j0 := eq557726 X0 X1 X2
       grind)
    | exact resolve eq557726 eq150550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150550 eq557726
  have eq558776 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (k (M.op X0 (M.op X1 X0)) X0) ∨ (M.op X0 (M.op X0 (M.op X1 X0))) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq558307 X1 x x
       have i₂ := eq31988 x X1 x x
       grind)
    | exact superpose eq31988 eq558307
    | (have j0 := eq558307 X0 X1 x
       grind)
    | exact resolve eq558307 eq31988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31988 eq558307
  have eq559139 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = (k (M.op X0 (M.op X1 X0)) X0) ∨ (M.op X0 (M.op X0 (M.op X1 X0))) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq558776 X0 X1
       have i₂ := eq9414 X0 X1 X1
       grind)
    | exact superpose eq9414 eq558776
    | (have j0 := eq558776 X0 X1
       grind)
    | exact resolve eq558776 eq9414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9414 eq558776
  have eq559331 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = (k (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq559139 X0 X1
       have j1 := eq314 (M.op X0 (M.op X1 X0)) X0
       grind)
    | (have r₁ := eq559139 X1 X1
       have r₂ := eq314 (M.op X1 (M.op X1 X1)) X1
       grind)
    | exact resolve eq559139 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314 eq559139
  have eq560123 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq559331 (M.op X0 x) (M.op X0 (M.op X0 X0))
       have i₂ := eq13623 X0 X0 x
       grind)
    | exact superpose eq13623 eq559331
    | exact resolve eq559331 eq13623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13623 eq559331
  have eq560332 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq560123 X0 X1
       have i₂ := eq3330 X1 X0
       grind)
    | exact superpose eq3330 eq560123
    | exact resolve eq560123 eq3330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3330 eq560123
  have eq566345 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (M.op X1 (σ X0))
       have i₂ := eq560332 (σ X0) X1
       grind)
    | exact superpose eq560332 eq30
    | exact resolve eq30 eq560332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq560332
  have eq566377 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k X0 (τ (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq566345 X0 X1
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq566345
    | exact resolve eq566345 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566345
  have eq566636 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq566377 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq566377
    | exact resolve eq566377 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566377
  have eq584560 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25690
       grind)
    | exact superpose eq25690 eq16
    | exact resolve eq16 eq25690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25690
  have eq897639 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24479
       have i₂ := eq121617 y x
       grind)
    | exact superpose eq121617 eq24479
    | (have j1 := eq121617 (σ y) (σ x)
       grind)
    | (have r₁ := eq24479
       have r₂ := eq121617 y x
       grind)
    | exact resolve eq24479 eq121617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24479 eq121617
  have eq897640 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq897639
  have eq897650 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq897640
       have r₂ := eq584560
       grind)
    | exact resolve eq897640 eq584560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584560 eq897640
  have eq897680 : (M.op y y) = (k y (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq566636 y (σ x)
       have i₂ := eq897650
       grind)
    | exact superpose eq897650 eq566636
    | exact resolve eq566636 eq897650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566636
  have eq898092 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op X0 (M.op (M.op X1 X0) (σ x)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq167390 X0 X1 (σ x) (σ y)
       have i₂ := eq897650
       grind)
    | exact superpose eq897650 eq167390
    | exact resolve eq167390 eq897650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897650
  have eq898117 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq898092 x x
       have i₂ := eq5572 x x (σ x)
       grind)
    | exact superpose eq5572 eq898092
    | exact resolve eq898092 eq5572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898092
  have eq898290 : (k y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq897680
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq897680
    | exact resolve eq897680 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897680
  have eq898308 : (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq898117
       have i₂ := eq56 y
       grind)
    | exact superpose eq56 eq898117
    | exact resolve eq898117 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq898117
  have eq898402 : (k y x) = (M.op y y) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq898290
       have r₂ := eq12 y x
       grind)
    | exact resolve eq898290 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898290
  have eq902311 : x ≠ (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq192462 y x
       have i₂ := eq898402
       grind)
    | exact superpose eq898402 eq192462
    | (have j0 := eq192462 y x
       grind)
    | exact resolve eq192462 eq898402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192462 eq898402
  have eq909495 : (M.op y y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq898308
       grind)
    | exact superpose eq898308 eq10
    | exact resolve eq10 eq898308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898308
  have eq909700 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq909495
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq909495
    | exact resolve eq909495 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909495
  have eq909756 : x = (M.op x y) := by
    first
    | (have r₁ := eq909700
       have r₂ := eq902311
       grind)
    | exact resolve eq909700 eq902311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902311 eq909700
  have eq911443 : ∀ X0 X1 : G, (M.op y y) = (M.op x (M.op X0 (M.op (M.op X1 X0) x))) := by
    intro X0 X1
    first
    | (have i₁ := eq167390 X0 X1 x y
       have i₂ := eq909756
       grind)
    | exact superpose eq909756 eq167390
    | exact resolve eq167390 eq909756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167390
  have eq911460 : x = (M.op y y) := by
    first
    | (have i₁ := eq911443 x x
       have i₂ := eq5572 x x x
       grind)
    | exact superpose eq5572 eq911443
    | exact resolve eq911443 eq5572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5572 eq911443
  have eq913287 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq841 y
       have i₂ := eq911460
       grind)
    | exact superpose eq911460 eq841
    | exact resolve eq841 eq911460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841 eq911460
  have eq978652 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq913287
       grind)
    | exact superpose eq913287 eq16
    | exact resolve eq16 eq913287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913287
  have eq979380 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq978652
       have i₂ := eq909756
       grind)
    | exact superpose eq909756 eq978652
    | exact resolve eq978652 eq909756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909756 eq978652
  have eq979381 : False := by grind
  exact eq979381
