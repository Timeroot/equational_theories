import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2592`: `x = (y ◇ ((z ◇ y) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(Y,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pxy_pxy_pyx_Equation2592 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2592 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2592.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X2)) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op y (M.op (M.op x y) x)) X0) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X0) X1) X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 X0) X1) X0
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : y ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
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
  have eq65 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k (M.op X1 (M.op (M.op X2 X1) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 (M.op (M.op X2 X1) X2)) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 (M.op X1 (M.op (M.op X2 X1) X2)) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op (M.op X2 X1) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq66 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq70 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq73
  have eq88 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq88
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq93
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq99
    | exact resolve eq99 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq215 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) x) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq222 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 (τ X1)) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 X0
       have i₂ := eq11 (τ X1) X0
       grind)
    | exact superpose eq11 eq34
    | (have j1 := eq11 (τ X1) X0
       grind)
    | exact resolve eq34 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq359 : ∀ X0 : G, X0 ≠ X0 ∨ (k (M.op (M.op (M.op x y) x) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq215 eq13
    | (have r₁ := eq13 (M.op (M.op (M.op x y) x) y) X0
       have r₂ := eq215 X0
       grind)
    | exact resolve eq13 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 : G, (k (M.op (M.op (M.op x y) x) y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq359 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq419 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 (M.op (M.op (M.op X1 X2) X1) X2) X3
       have i₂ := eq53 X2 X1 X0
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) = (k X0 (M.op (M.op (M.op X1 X2) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq102 X0 (M.op (M.op (M.op X1 X2) X1) X2)
       have i₂ := eq53 X2 X1 X0
       grind)
    | exact superpose eq53 eq102
    | (have j0 := eq102 X0 (M.op (M.op (M.op X1 X2) X1) X2)
       grind)
    | (have r₁ := eq102 X2 (M.op (M.op (M.op X1 X0) X1) X0)
       have r₂ := eq53 X0 X1 X2
       grind)
    | exact resolve eq102 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k (M.op (M.op (M.op X1 X2) X1) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op (M.op X1 X0) X1) X0) X2
       have i₂ := eq53 X0 X1 X2
       grind)
    | exact superpose eq53 eq13
    | (have r₁ := eq13 (M.op (M.op (M.op X1 X0) X1) X0) X2
       have r₂ := eq53 X0 X1 X2
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op X1 X2) X1) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq433 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq437 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X1) X2)) = (k X0 (M.op (M.op (M.op X1 X2) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq432 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq482 : ∀ X0 X1 : G, (k (M.op (M.op X0 (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x)))) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq67
    | exact resolve eq67 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq1126 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (M.op (M.op (M.op X1 X2) X1) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq245 (M.op (M.op (M.op X1 X2) X1) X2) X0
       have i₂ := eq436 (σ X0) X1 X2
       grind)
    | exact superpose eq436 eq245
    | exact resolve eq245 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq1129 : ∀ X0 X1 X2 : G, (k (τ (M.op (M.op (M.op X1 X2) X1) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1126 X0 X1 X2
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq1126
    | exact resolve eq1126 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq2196 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (M.op X1 (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x)))) X1)) X0) := by
    intro X0 X1
    first
    | exact superpose eq482 eq245
    | exact resolve eq245 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq482
  have eq2199 : ∀ X0 X1 : G, (k (τ (M.op (M.op X1 (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x)))) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2196 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq2196
    | exact resolve eq2196 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2196
  have eq17623 : (τ (k (σ x) (σ x))) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq16
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq17648 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq49 eq17623
    | exact resolve eq17623 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq17623
  have eq17651 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq17648
       have r₂ := eq13 x x
       grind)
    | exact resolve eq17648 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17648
  have eq17652 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq17651
       grind)
    | exact superpose eq17651 eq43
    | exact resolve eq43 eq17651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17651
  have eq19229 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19230 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq19229
    | exact resolve eq19229 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19229
  have eq19241 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq19230
       have r₂ := eq27
       grind)
    | exact resolve eq19230 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19230
  have eq19243 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq19241
    | exact resolve eq19241 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19241
  have eq19245 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq19243 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19243
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19243
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19243
       grind)
    | exact resolve eq13 eq19243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19248 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq19243 eq53
    | exact resolve eq53 eq19243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19243
  have eq19277 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq19245
  have eq19305 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq19248
    | (have j0 := eq19248 X0
       grind)
    | exact resolve eq19248 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19248
  have eq19780 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq19277 eq101
    | exact resolve eq101 eq19277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq19277
  have eq19793 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19780
  have eq19810 : ∀ X0 : G, (M.op (M.op (M.op x y) x) X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq53 x y X0
       have i₂ := eq19793
       grind)
    | exact superpose eq19793 eq53
    | exact resolve eq53 eq19793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19813 : x ≠ x ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq102 x y
       have i₂ := eq19793
       grind)
    | exact superpose eq19793 eq102
    | (have j0 := eq102 x y
       grind)
    | (have r₁ := eq102 x y
       have r₂ := eq19793
       grind)
    | (have r₁ := eq102 y x
       have r₂ := eq19793
       grind)
    | (have r₁ := eq102 (σ y) (σ x)
       have r₂ := eq19793
       grind)
    | exact resolve eq102 eq19793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19793
  have eq19839 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19813
  have eq19867 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19839
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19839
    | exact resolve eq19839 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19839
  have eq19870 : ∀ X0 : G, (M.op (M.op (M.op x y) x) X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19810 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19810
    | (have j0 := eq19810 X0
       grind)
    | exact resolve eq19810 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19810
  have eq19873 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq19867
       have r₂ := eq64
       grind)
    | exact resolve eq19867 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19867
  have eq19876 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq19873
       grind)
    | exact superpose eq19873 eq44
    | exact resolve eq44 eq19873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq19873
  have eq19895 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq19876
    | exact resolve eq19876 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19876
  have eq19987 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq70 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq70
    | (have j0 := eq70 x
       grind)
    | exact resolve eq70 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19996 : ∀ X0 : G, (σ x) ≠ (σ (k x X0)) ∨ (k (σ x) (σ X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq70 eq102
    | (have j0 := eq102 (σ x) (σ X0)
       have j1 := eq70 X0
       grind)
    | (have r₁ := eq102 (σ x) (σ X0)
       have r₂ := eq70 X0
       grind)
    | (have r₁ := eq102 (σ X0) (σ x)
       have r₂ := eq70 X0
       grind)
    | exact resolve eq102 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq20023 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq19987
  have eq20024 : ∀ X0 : G, (σ x) ≠ (σ (k x X0)) ∨ (k (σ x) (σ X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have j0 := eq19996 X0
       have j1 := eq13 (σ x) (σ X0)
       grind)
    | (have r₁ := eq19996 X0
       have r₂ := eq13 (σ X0) (σ x)
       grind)
    | (have r₁ := eq19996 X0
       have r₂ := eq13 (σ x) (σ X0)
       grind)
    | exact resolve eq19996 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19996
  have eq20028 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq20023
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq20023
    | exact resolve eq20023 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq20023
  have eq20052 : ∀ X0 : G, (σ x) ≠ (σ (k x X0)) ∨ (k (σ x) (σ X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq20024 X0
       have j1 := eq102 (σ x) (σ X0)
       grind)
    | (have r₁ := eq20024 X0
       have r₂ := eq102 (σ x) (σ X0)
       grind)
    | exact resolve eq20024 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20024
  have eq20053 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq20028
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq20028 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20028
  have eq20057 : ∀ X0 : G, (σ x) ≠ (σ (k x X0)) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq20052
    | (have j0 := eq20052 X0
       grind)
    | exact resolve eq20052 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq20052
  have eq20075 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19895 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq19895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20076 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq20075
    | exact resolve eq20075 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20075
  have eq20077 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq20076
  have eq20934 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq191 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq21808 : ∀ X0 : G, (k y X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq19870 eq362
    | exact resolve eq362 eq19870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq19870
  have eq22494 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq242 X0 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq242
    | exact resolve eq242 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq22619 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22494 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq22494
    | (have j0 := eq22494 X0 X1
       grind)
    | exact resolve eq22494 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22494
  have eq45843 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20077 eq102
    | (have j0 := eq102 (σ x) (σ y)
       grind)
    | (have r₁ := eq102 (σ x) (σ y)
       have r₂ := eq20077
       grind)
    | (have r₁ := eq102 (σ y) (σ x)
       have r₂ := eq20077
       grind)
    | exact resolve eq102 eq20077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20077
  have eq45884 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq45843
  have eq45925 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq45884
    | exact resolve eq45884 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45884
  have eq45931 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq45925
       have r₂ := eq65
       grind)
    | exact resolve eq45925 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq45925
  have eq46651 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq45931 eq19895
    | exact resolve eq19895 eq45931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45931
  have eq46670 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq46651
  have eq46686 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq46670
       have r₂ := eq27
       grind)
    | exact resolve eq46670 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46670
  have eq152519 : ∀ X0 : G, x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq19305 eq222
    | exact resolve eq222 eq19305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19305
  have eq153052 : ∀ X0 : G, x ≠ x ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq102 x y
       have i₂ := eq152519 X0
       grind)
    | exact superpose eq152519 eq102
    | (have j0 := eq102 x y
       have j1 := eq152519 X0
       grind)
    | (have r₁ := eq102 x y
       have r₂ := eq152519 X0
       grind)
    | (have r₁ := eq102 (σ y) (σ x)
       have r₂ := eq152519 X0
       grind)
    | (have r₁ := eq102 y x
       have r₂ := eq152519 X0
       grind)
    | exact resolve eq102 eq152519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152519
  have eq153104 : ∀ X0 : G, (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq153052 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153052
  have eq153158 : ∀ X0 : G, (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq153104 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq153104
    | (have j0 := eq153104 X0
       grind)
    | exact resolve eq153104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153104
  have eq153164 : ∀ X0 : G, (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq153158 X0
       grind)
    | (have r₁ := eq153158 X0
       have r₂ := eq64
       grind)
    | exact resolve eq153158 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq153158
  have eq153203 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20057 y
       have i₂ := eq153164 X0
       grind)
    | (have i₁ := eq20057 X0
       have i₂ := eq153164 (k x X0)
       grind)
    | exact superpose eq153164 eq20057
    | (have j1 := eq153164 X0
       grind)
    | exact resolve eq20057 eq153164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153164
  have eq153244 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq153203
    | (have j0 := eq153203 X0
       grind)
    | exact resolve eq153203 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153203
  have eq153264 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq153244 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq153244
    | (have j0 := eq153244 X0
       grind)
    | exact resolve eq153244 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153244
  have eq153276 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq153264
    | (have j0 := eq153264 X0
       grind)
    | exact resolve eq153264 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153264
  have eq153286 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq153276
    | (have j0 := eq153276 X0
       grind)
    | exact resolve eq153276 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153276
  have eq153296 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq153286 X0
       grind)
    | (have r₁ := eq153286 X0
       have r₂ := eq27
       grind)
    | exact resolve eq153286 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153286
  have eq479077 : (σ (σ (M.op x y))) = (σ (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19895 eq22619
    | (have j0 := eq22619 (σ x) (σ y)
       grind)
    | exact resolve eq22619 eq19895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19895 eq22619
  have eq480218 : (σ (σ (M.op x y))) = (σ (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq153296 (σ x)
       grind)
    | (have r₁ := eq479077
       have r₂ := eq153296 x
       grind)
    | exact resolve eq479077 eq153296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479077
  have eq480430 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (σ (M.op x y))) = (σ (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq480218
    | exact resolve eq480218 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480218
  have eq480431 : (σ (σ (M.op x y))) = (σ (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq480430
  have eq480508 : (M.op (σ y) (σ x)) = (τ (σ (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq480431 eq16
    | exact resolve eq16 eq480431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480431
  have eq480733 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq480508
       have i₂ := eq16 sF1
       grind)
    | exact superpose eq16 eq480508
    | exact resolve eq480508 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480508
  have eq480808 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq480733
  have eq480815 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq480808
       have r₂ := eq46686
       grind)
    | exact resolve eq480808 eq46686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46686 eq480808
  have eq562928 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20934 y
       have i₂ := eq21808 y
       grind)
    | exact superpose eq21808 eq20934
    | (have j0 := eq20934 y
       grind)
    | exact resolve eq20934 eq21808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20934 eq21808
  have eq563132 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq562928
  have eq563297 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq153296 (σ y)
       grind)
    | (have r₁ := eq563132
       have r₂ := eq153296 x
       grind)
    | exact resolve eq563132 eq153296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153296 eq563132
  have eq563483 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq563297
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq563297
    | exact resolve eq563297 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563297
  have eq563622 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq563483
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq563483
    | exact resolve eq563483 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563483
  have eq563623 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq563622
  have eq563816 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ y) (σ y))) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq563623 eq14
    | exact resolve eq14 eq563623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq563818 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ y)) (σ y)) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq563623 eq53
    | exact resolve eq53 eq563623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq563909 : ∀ X0 : G, (M.op (M.op (σ y) (σ y)) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq563623 eq563816
    | exact resolve eq563816 eq563623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563816
  have eq564508 : ∀ X0 : G, (M.op (M.op (σ y) (σ y)) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq563909 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563909
  have eq565711 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq563623 eq564508
    | exact resolve eq564508 eq563623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563623 eq564508
  have eq566306 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq565711 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565711
  have eq566483 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq566306 eq480815
    | exact resolve eq480815 eq566306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480815
  have eq566503 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq566306 eq102
    | (have j0 := eq102 X0 (σ y)
       grind)
    | (have r₁ := eq102 X0 (σ y)
       have r₂ := eq566306 X0
       grind)
    | (have r₁ := eq102 y x
       have r₂ := eq566306 X0
       grind)
    | (have r₁ := eq102 (σ y) (σ x)
       have r₂ := eq566306 X0
       grind)
    | exact resolve eq102 eq566306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566992 : ∀ X0 : G, (k (τ (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) (σ y))) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq566306 eq2199
    | exact resolve eq2199 eq566306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2199
  have eq567005 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq566503 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566503
  have eq567018 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq566483
  have eq567040 : ∀ X0 : G, (k (τ (σ y)) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq51 eq566992
    | exact resolve eq566992 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq566992
  have eq567169 : ∀ X0 : G, (k y X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq29 eq567040
    | exact resolve eq567040 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq567040
  have eq644769 : (σ y) = (M.op y (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq567005 eq567169
    | exact resolve eq567169 eq567005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567005 eq567169
  have eq645027 : (σ y) = (M.op y (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq644769
  have eq824911 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ y)) X0) X1) = X1 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq563818 eq419
    | exact resolve eq419 eq563818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563818
  have eq827359 : ∀ X0 : G, (M.op (M.op (σ y) y) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq645027 eq824911
    | exact resolve eq824911 eq645027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645027 eq824911
  have eq828582 : ∀ X0 : G, (M.op (M.op (σ y) y) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq827359 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827359
  have eq829075 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq566306 eq828582
    | exact resolve eq828582 eq566306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566306 eq828582
  have eq829956 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq829075 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829075
  have eq830245 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 y) = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq102 X0 y
       have i₂ := eq829956 X0
       grind)
    | exact superpose eq829956 eq102
    | (have j0 := eq102 X0 y
       grind)
    | (have r₁ := eq102 X0 y
       have r₂ := eq829956 X0
       grind)
    | (have r₁ := eq102 y x
       have r₂ := eq829956 X0
       grind)
    | (have r₁ := eq102 (σ y) (σ x)
       have r₂ := eq829956 X0
       grind)
    | exact resolve eq102 eq829956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq829956
  have eq831037 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq830245 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830245
  have eq836151 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20057 y
       have i₂ := eq831037 x
       grind)
    | exact superpose eq831037 eq20057
    | exact resolve eq20057 eq831037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20057 eq831037
  have eq837118 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq836151
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq836151
    | exact resolve eq836151 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836151
  have eq837205 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq837118
    | exact resolve eq837118 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837118
  have eq837226 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq837205
       have r₂ := eq567018
       grind)
    | exact resolve eq837205 eq567018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567018 eq837205
  have eq837231 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq837226
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq837226
    | exact resolve eq837226 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837226
  have eq837234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq837231
    | exact resolve eq837231 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837231
  have eq837236 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq837234
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq837234
    | exact resolve eq837234 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837234
  have eq837238 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq837236
    | exact resolve eq837236 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837236
  have eq837239 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq837238
       have r₂ := eq27
       grind)
    | exact resolve eq837238 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837238
  have eq837244 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ x)) (σ y)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq837239 eq222
    | exact resolve eq222 eq837239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq837239
  have eq851468 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f851468_13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X0) X1) X0) X2) = X2 := by
      intro X0 X1 X2
      grind
    have f851468_14 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ x)) (σ y)) X0) = X0 ∨ y = (M.op x y) := by
      intro X0
      grind
    have f851468_23 : X0 ≠ (M.op (σ x) X0) := by grind
    have f851468_24 : y ≠ (M.op x y) := by grind
    have f851468_26 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ x)) (σ y)) X0) = X0 := by
      intro X0
      first
      | (have j0 := f851468_14 X0
         grind)
      | (have r₁ := f851468_14 X0
         have r₂ := f851468_24
         grind)
      | exact resolve f851468_14 f851468_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f851468_91 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
      intro X0
      first
      | (have i₁ := f851468_13 (σ x) (σ y) X0
         have i₂ := f851468_26 (σ x)
         grind)
      | exact superpose f851468_26 f851468_13
      | exact resolve f851468_13 f851468_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f851468_99 : X0 ≠ X0 := by
      first
      | (have i₁ := f851468_23
         have i₂ := f851468_91 X0
         grind)
      | exact superpose f851468_91 f851468_23
      | (have r₁ := f851468_23
         have r₂ := f851468_91 X0
         grind)
      | exact resolve f851468_23 f851468_91
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f851468_108 : False := by grind
    exact f851468_108
  have eq851469 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ x)) X0) X1) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq837244 eq419
    | exact resolve eq419 eq837244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq851472 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq837244 eq437
    | exact resolve eq437 eq837244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq851482 : ∀ X0 : G, (k (τ (σ x)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq837244 eq1129
    | exact resolve eq1129 eq837244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129 eq837244
  have eq852583 : ∀ X0 : G, (k x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28 eq851482
    | exact resolve eq851482 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq851482
  have eq860353 : (σ x) = (M.op x (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq851472 eq852583
    | exact resolve eq852583 eq851472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851472 eq852583
  have eq860691 : (σ x) = (M.op x (σ x)) ∨ y = (M.op x y) := by grind
  clear eq860353
  have eq912787 : ∀ X0 : G, (M.op (M.op (σ x) x) X0) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq860691 eq851469
    | exact resolve eq851469 eq860691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851469 eq860691
  have eq914009 : ∀ X0 : G, (M.op (M.op (σ x) x) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq912787 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912787
  have eq916080 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq851468 eq914009
    | exact resolve eq914009 eq851468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851468 eq914009
  have eq916947 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq916080 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916080
  have eq917184 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq916947 y
       grind)
    | exact superpose eq916947 eq18
    | (have j1 := eq916947 y
       grind)
    | exact resolve eq18 eq916947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq916947
  have eq918051 : y = (M.op x y) := by grind
  clear eq917184
  have eq918315 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq918051 eq20
    | exact resolve eq20 eq918051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq918367 : ∀ X0 : G, (M.op (M.op (M.op y x) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq918051 eq215
    | exact resolve eq215 eq918051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq918051
  have eq918764 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq918315
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq918315
    | exact resolve eq918315 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq918315
  have eq919483 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq918764 eq26
    | exact resolve eq26 eq918764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq918764
  have eq928896 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 x y X0
       have i₂ := eq918367 x
       grind)
    | exact superpose eq918367 eq53
    | exact resolve eq53 eq918367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918367
  have eq930473 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq17652
       have i₂ := eq928896 x
       grind)
    | exact superpose eq928896 eq17652
    | exact resolve eq17652 eq928896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17652 eq928896
  have eq931989 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20053 eq930473
    | exact resolve eq930473 eq20053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20053 eq930473
  have eq932018 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq931989
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq931989
    | exact resolve eq931989 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq931989
  have eq947547 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ x)) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq932018 eq53
    | exact resolve eq53 eq932018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq947699 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq932018 eq947547
    | exact resolve eq947547 eq932018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947547
  have eq947776 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq932018 eq947699
    | exact resolve eq947699 eq932018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932018 eq947699
  have eq947908 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq947776 eq919483
    | exact resolve eq919483 eq947776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919483 eq947776
  have eq949422 : False := by grind
  exact eq949422

/-- `Equation2646`: `x = ((x ◇ x) ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation2646 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2646 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2646.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq35 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq22
    | exact resolve eq22 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq47
    | exact resolve eq47 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq70 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq100 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq97
    | (have j0 := eq97 X0 X1
       grind)
    | exact resolve eq97 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq137 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100 X0 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq137 X0 X1 X2
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq137
    | (have j0 := eq137 X0 X1 X2
       grind)
    | exact resolve eq137 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq137
  have eq164 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq100 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq48 X0
       grind)
    | exact superpose eq48 eq100
    | (have j0 := eq100 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq100 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq165 : ∀ X0 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq13 (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)
       have i₂ := eq48 X0
       grind)
    | exact superpose eq48 eq13
    | (have j0 := eq13 (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)
       grind)
    | exact resolve eq13 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq165 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq165
    | (have j0 := eq165 X0
       grind)
    | exact resolve eq165 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq174 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) ∨ (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq168 X0
       have i₂ := eq15 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       grind)
    | exact superpose eq15 eq168
    | (have j0 := eq168 X0
       grind)
    | exact resolve eq168 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq178 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq174
    | (have j0 := eq174 X0
       grind)
    | exact resolve eq174 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq3454 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) (k (σ X1) X2)) ≠ (M.op X3 (k (σ X1) X2)) ∨ (M.op (σ X0) (k (σ X1) X2)) = (k X3 (k (σ X1) X2)) ∨ (k (σ X1) X2) = X3 ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 (k (σ X0) X1)
       have i₂ := eq147 X0 X1 X2
       grind)
    | exact superpose eq147 eq13
    | (have j0 := eq13 (M.op (σ X0) (k (σ X1) X2)) (k X3 (k (σ X1) X2))
       have j1 := eq147 X1 X2 X0
       grind)
    | (have r₁ := eq13 (σ X2) (k (σ X0) X1)
       have r₂ := eq147 X0 X1 X2
       grind)
    | exact resolve eq13 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq50938 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 X0
       have i₂ := eq164 X0
       grind)
    | exact superpose eq164 eq48
    | (have j1 := eq164 X0
       grind)
    | exact resolve eq48 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq164
  have eq51161 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq50938 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq50938
    | (have j0 := eq50938 X0
       grind)
    | exact resolve eq50938 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50938
  have eq51162 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have j0 := eq51161 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51161
  have eq62337 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq51162 X0
       grind)
    | exact superpose eq51162 eq178
    | (have j0 := eq178 X0
       have j1 := eq51162 X0
       grind)
    | (have r₁ := eq178 X0
       have r₂ := eq51162 X0
       grind)
    | exact resolve eq178 eq51162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq51162
  have eq62344 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq62337 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62337
  have eq62345 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have j0 := eq62344 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62344
  have eq89556 : ∀ X0 : G, (σ (τ X0)) = (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) ∨ (σ (τ X0)) = (σ (k (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq62345 (τ X0)
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq62345
    | exact resolve eq62345 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq62345
  have eq89852 : ∀ X0 : G, (σ (τ X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (σ (τ X0)) = (σ (k (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq89556 X0
       have i₂ := eq30 (M.op X0 X0)
       grind)
    | exact superpose eq30 eq89556
    | (have j0 := eq89556 X0
       grind)
    | exact resolve eq89556 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89556
  have eq89860 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (σ (τ X0)) = (σ (k (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq89852 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq89852
    | (have j0 := eq89852 X0
       grind)
    | exact resolve eq89852 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89852
  have eq89865 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) X0) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq89860 X0
       have i₂ := eq19 X0 (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))
       grind)
    | exact superpose eq19 eq89860
    | (have j0 := eq89860 X0
       grind)
    | exact resolve eq89860 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89860
  have eq89869 : ∀ X0 : G, (σ (τ X0)) = (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq89865 X0
       have i₂ := eq30 (M.op X0 X0)
       grind)
    | exact superpose eq30 eq89865
    | (have j0 := eq89865 X0
       grind)
    | exact resolve eq89865 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq89865
  have eq89871 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq89869 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq89869
    | (have j0 := eq89869 X0
       grind)
    | exact resolve eq89869 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89869
  have eq220591 : ∀ X0 X1 X2 : G, (k (σ X0) (k (σ X1) X2)) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3454 X0 X1 X2 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3454
  have eq220592 : ∀ X0 X1 X2 : G, (k (σ X0) (k (σ X1) X2)) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq220591 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220591
  have eq220598 : ∀ X0 X1 X2 : G, (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) ∨ (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq220592 X0 X1 X2
       have i₂ := eq35 X1 X2 X0
       grind)
    | exact superpose eq35 eq220592
    | (have j0 := eq220592 X0 X1 X2
       grind)
    | exact resolve eq220592 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq220592
  have eq220599 : ∀ X0 X1 X2 : G, (σ (k X0 (k X1 (τ X2)))) = (M.op (σ X0) (k (σ X1) X2)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq220598 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220598
  have eq221082 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 (τ X2)))) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (k X1 (τ X2))
       have i₂ := eq220599 (τ X0) X1 X2
       grind)
    | exact superpose eq220599 eq18
    | (have j1 := eq220599 (τ X0) X1 X2
       grind)
    | exact resolve eq18 eq220599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq220599
  have eq221437 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 (τ X2)))) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq221082 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq221082
    | (have j0 := eq221082 X0 X1 X2
       grind)
    | exact resolve eq221082 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221082
  have eq221620 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq221437 X0 X1 X2
       have i₂ := eq19 X2 X1
       grind)
    | exact superpose eq19 eq221437
    | (have j0 := eq221437 X0 X1 X2
       grind)
    | exact resolve eq221437 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221437
  have eq221741 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) ∨ (k (σ X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq221620 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq221620
    | (have j0 := eq221620 X0 X1 X2
       grind)
    | exact resolve eq221620 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221620
  have eq222034 : ∀ X0 X1 X2 : G, (k X1 (k X0 X2)) = (M.op X1 (k X0 X2)) ∨ (k X0 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq221741 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq221741
    | exact resolve eq221741 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221741
  have eq223349 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq223914 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq223349 (M.op X0 X0) X1
       have i₂ := eq89871 X0
       grind)
    | exact superpose eq89871 eq223349
    | (have j1 := eq89871 X0
       grind)
    | exact resolve eq223349 eq89871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89871 eq223349
  have eq255757 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ X0 = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq222034 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X0
       have i₂ := eq223914 X0 X1
       grind)
    | exact superpose eq223914 eq222034
    | (have j0 := eq222034 X1 (M.op X1 X0) X0
       have j1 := eq223914 X0 X1
       grind)
    | exact resolve eq222034 eq223914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222034 eq223914
  have eq258031 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq255757 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255757
  have eq258032 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq258031 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258031
  have eq258033 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq258032 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258032
  have eq258305 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq258033 X0 (τ X1)
       grind)
    | exact superpose eq258033 eq19
    | (have j1 := eq258033 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq258033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq258606 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq258033 (σ X0) (σ X1)
       grind)
    | exact superpose eq258033 eq15
    | (have j1 := eq258033 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq258033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258033
  have eq262088 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq258305 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq258305
    | exact resolve eq258305 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258305
  have eq262602 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq262088 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq262088
    | (have j0 := eq262088 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq262088 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262088
  have eq267116 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq258606 x y
       grind)
    | exact superpose eq258606 eq16
    | (have j1 := eq258606 x y
       grind)
    | exact resolve eq16 eq258606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258606
  have eq267297 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq267116
       have i₂ := eq262602 y x
       grind)
    | exact superpose eq262602 eq267116
    | (have j1 := eq262602 (σ x) (σ y)
       grind)
    | (have r₁ := eq267116
       have r₂ := eq262602 y x
       grind)
    | (have r₁ := eq267116
       have r₂ := eq262602 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq267116
       have r₂ := eq262602 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq267116 eq262602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262602 eq267116
  have eq267300 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq267297
  have eq267943 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq267300
       grind)
    | exact superpose eq267300 eq16
    | exact resolve eq16 eq267300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267300
  have eq267944 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq267943
       have r₂ := eq22 x
       grind)
    | exact resolve eq267943 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267943
  have eq267945 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq267944
       grind)
    | exact superpose eq267944 eq16
    | exact resolve eq16 eq267944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267946 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq267944
       grind)
    | exact superpose eq267944 eq10
    | exact resolve eq10 eq267944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267944
  have eq268356 : x = y := by
    first
    | (have i₁ := eq267946
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq267946
    | exact resolve eq267946 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267946
  have eq268357 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq267945
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq267945
    | exact resolve eq267945 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq267945
  have eq268364 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq268357
       have i₂ := eq268356
       grind)
    | exact superpose eq268356 eq268357
    | exact resolve eq268357 eq268356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268356 eq268357
  have eq268365 : False := by grind
  exact eq268365

/-- `Equation2646`: `x = ((x ◇ x) ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation2646 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2646 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2646.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq155 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq157 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
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
  have eq735 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq155 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq812 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) X0
       have i₂ := eq157 X1 X0
       grind)
    | exact superpose eq157 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq157 X1 X0
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq157 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X0)
       have r₂ := eq157 X0 (M.op X0 (τ X0))
       grind)
    | exact resolve eq13 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq814 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq812 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq815 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (k (τ X1) X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq814 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq2358 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq815 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq815
    | exact resolve eq815 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq2407 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2358 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2358
    | (have j0 := eq2358 X0 X1
       grind)
    | exact resolve eq2358 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2358
  have eq2447 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq2407 X0 X1
       grind)
    | exact superpose eq2407 eq10
    | (have j1 := eq2407 X0 X1
       grind)
    | exact resolve eq10 eq2407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2491 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2447 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2447
    | (have j0 := eq2447 X0 X1
       grind)
    | exact resolve eq2447 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2447
  have eq2530 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq2491 (σ X0) X1
       grind)
    | exact superpose eq2491 eq37
    | (have j1 := eq2491 (σ X0) X1
       grind)
    | exact resolve eq37 eq2491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2491
  have eq4359 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X1) X0
       have i₂ := eq2530 X1 (σ X0)
       grind)
    | exact superpose eq2530 eq28
    | (have j1 := eq2530 X1 (σ X0)
       grind)
    | exact resolve eq28 eq2530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2530
  have eq4420 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4359 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4359
    | (have j0 := eq4359 X0 X1
       grind)
    | exact resolve eq4359 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4359
  have eq4454 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4420 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4420
    | (have j0 := eq4420 X0 X1
       grind)
    | exact resolve eq4420 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4420
  have eq4464 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4454 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4454
    | (have j0 := eq4454 X0 X1
       grind)
    | exact resolve eq4454 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4454
  have eq4670 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq4464 X1 X0
       grind)
    | exact superpose eq4464 eq11
    | (have j1 := eq4464 X1 X0
       grind)
    | exact resolve eq11 eq4464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4464
  have eq5592 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4670 x y
       grind)
    | exact superpose eq4670 eq16
    | (have j1 := eq4670 x y
       grind)
    | exact resolve eq16 eq4670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4670
  have eq5628 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5592
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq5592
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq5592
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5592
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5592 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5629 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq5592
       have i₂ := eq2407 x y
       grind)
    | exact superpose eq2407 eq5592
    | (have j1 := eq2407 x y
       grind)
    | (have r₁ := eq5592
       have r₂ := eq2407 x y
       grind)
    | (have r₁ := eq5592
       have r₂ := eq2407 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5592
       have r₂ := eq2407 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5592 eq2407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2407 eq5592
  have eq5632 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5629
  have eq5633 : x = y ∨ (σ x) = (σ y) ∨ y = (k x y) := by grind
  clear eq5632
  have eq5634 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5628
  have eq5635 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq5634
  have eq5639 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5633
       grind)
    | exact superpose eq5633 eq16
    | exact resolve eq16 eq5633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5633
  have eq5640 : y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5639
       have r₂ := eq22 x
       grind)
    | exact resolve eq5639 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5639
  have eq5644 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq735 x y
       have i₂ := eq5640
       grind)
    | exact superpose eq5640 eq735
    | (have j0 := eq735 x y
       grind)
    | exact resolve eq735 eq5640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735 eq5640
  have eq5651 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5644
  have eq5652 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5651
  have eq5656 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5635
       grind)
    | exact superpose eq5635 eq16
    | exact resolve eq16 eq5635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5635
  have eq5657 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5656
       have r₂ := eq22 x
       grind)
    | exact resolve eq5656 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5656
  have eq5667 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5652
       grind)
    | exact superpose eq5652 eq16
    | exact resolve eq16 eq5652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5652
  have eq5692 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5667
       have i₂ := eq5657
       grind)
    | exact superpose eq5657 eq5667
    | exact resolve eq5667 eq5657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5657 eq5667
  have eq5693 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq5692
  have eq5694 : (σ x) = (σ y) := by grind
  clear eq5693
  have eq5695 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5694
       grind)
    | exact superpose eq5694 eq16
    | exact resolve eq16 eq5694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5696 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5694
       grind)
    | exact superpose eq5694 eq10
    | exact resolve eq10 eq5694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5694
  have eq5751 : x = y := by
    first
    | (have i₁ := eq5696
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5696
    | exact resolve eq5696 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5696
  have eq5752 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5695
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5695
    | exact resolve eq5695 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5695
  have eq5753 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5752
       have i₂ := eq5751
       grind)
    | exact superpose eq5751 eq5752
    | exact resolve eq5752 eq5751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5751 eq5752
  have eq5754 : False := by grind
  exact eq5754

/-- `Equation2653`: `x = ((x ◇ x) ◇ (y ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxy_pyy_pxy_Equation2653 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2653 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2653.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X1) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq9 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq9
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X0)) (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0)
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq9
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq9
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq89 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
    | (have r₁ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq89
    | (have j0 := eq89 (σ X0) (σ X1)
       grind)
    | exact resolve eq89 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k X2 X0) = (M.op X2 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X0
       have i₂ := eq89 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq89 X0 (M.op X1 X1)
       grind)
    | exact superpose eq89 eq12
    | (have j0 := eq12 X2 X0
       have j1 := eq89 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq89 X1 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq89 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq59 (M.op (M.op X0 X0) X0) X0
       have i₂ := eq58 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq58 eq59
    | exact resolve eq59 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq59
  have eq214 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq211 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq211
    | exact resolve eq211 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq230 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq214 X0
       grind)
    | exact superpose eq214 eq9
    | exact resolve eq9 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq280 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0
       have i₂ := eq230 X0 X1
       grind)
    | exact superpose eq230 eq56
    | exact resolve eq56 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq230
  have eq343 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq280 (M.op X0 X0) x
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq280
    | exact resolve eq280 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq669 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq98 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq683 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq669 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq684 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq683 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq690 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq684 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq684
    | exact resolve eq684 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq690 X0
       have i₂ := eq684 X0
       grind)
    | exact superpose eq684 eq690
    | exact resolve eq690 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684 eq690
  have eq750 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq913 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq343 (σ X0)
       have i₂ := eq693 X0
       grind)
    | exact superpose eq693 eq343
    | exact resolve eq343 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1886 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq750
       have i₂ := eq693 x
       grind)
    | exact superpose eq693 eq750
    | exact resolve eq750 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693 eq750
  have eq1961 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1886
       have i₂ := eq89 x y
       grind)
    | exact superpose eq89 eq1886
    | (have j1 := eq89 x y
       grind)
    | exact resolve eq1886 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq1886
  have eq1979 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq1961
  have eq1987 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1979
       grind)
    | exact superpose eq1979 eq10
    | exact resolve eq10 eq1979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1979
  have eq2014 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1987
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1987
    | exact resolve eq1987 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1987
  have eq2015 : y = (M.op x x) := by grind
  clear eq2014
  have eq2040 : y = (M.op x y) := by
    first
    | (have i₁ := eq343 x
       have i₂ := eq2015
       grind)
    | exact superpose eq2015 eq343
    | exact resolve eq343 eq2015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq2057 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq913 x
       have i₂ := eq2015
       grind)
    | exact superpose eq2015 eq913
    | exact resolve eq913 eq2015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913 eq2015
  have eq2200 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2057
       grind)
    | exact superpose eq2057 eq16
    | exact resolve eq16 eq2057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057
  have eq2206 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2200
       have i₂ := eq2040
       grind)
    | exact superpose eq2040 eq2200
    | exact resolve eq2200 eq2040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040 eq2200
  have eq2207 : False := by grind
  exact eq2207

/-- `Equation2653`: `x = ((x ◇ x) ◇ (y ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_pyx_pxy_Equation2653 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2653 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2653.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X1) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq94 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq9 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq94 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq94
    | exact resolve eq94 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq94 (M.op X0 X0)
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq94
    | exact resolve eq94 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq9
    | exact resolve eq9 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X0)) (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0)
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq9
    | exact resolve eq9 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X1
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq9
    | exact resolve eq9 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq95 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq95
    | exact resolve eq95 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq104 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq102
    | exact resolve eq102 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq276 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq100 (M.op (M.op X0 X0) X0) X0
       have i₂ := eq99 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq99 eq100
    | exact resolve eq100 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq278 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq276 X0
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq276
    | exact resolve eq276 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq276
  have eq281 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq324 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq281 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq281
    | (have j0 := eq281 X0 X1
       grind)
    | exact resolve eq281 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq328 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq278 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq278
    | exact resolve eq278 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq278 X0
       grind)
    | exact superpose eq278 eq9
    | exact resolve eq9 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq94 (M.op (M.op X0 X0) X0)
       have i₂ := eq278 X0
       grind)
    | exact superpose eq278 eq94
    | exact resolve eq94 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq354 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq328 X0
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq328
    | exact resolve eq328 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq357 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq354 X0
       have i₂ := eq22 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq22 eq354
    | exact resolve eq354 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq359 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq357 X0
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq357
    | exact resolve eq357 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq362 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 (M.op (M.op X0 X0) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq343 (M.op (M.op X0 X0) X0)
       have i₂ := eq278 X0
       grind)
    | exact superpose eq278 eq343
    | exact resolve eq343 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq362 X0
       have i₂ := eq343 X0
       grind)
    | exact superpose eq343 eq362
    | exact resolve eq362 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq384 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) = (M.op (M.op X1 X0) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq331 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq278 X0
       grind)
    | exact superpose eq278 eq331
    | exact resolve eq331 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X1) (M.op (M.op X0 (M.op X1 X1)) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq278 X0
       have i₂ := eq331 X0 X1
       grind)
    | exact superpose eq331 eq278
    | exact resolve eq278 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq331
  have eq2110 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 X0)) = (M.op (M.op (M.op X1 X1) X1) (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq384 (M.op (M.op X0 X0) X0) (M.op X1 X0)
       have i₂ := eq384 X0 X1
       grind)
    | exact superpose eq384 eq384
    | exact resolve eq384 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq2173 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 X0)) = (M.op (M.op (M.op X1 X1) X1) (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2110 X0 X1
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq2110
    | exact resolve eq2110 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq2110
  have eq2191 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 X0)) = (M.op (M.op (M.op X1 X1) X1) (M.op X0 (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2173 X0 X1
       have i₂ := eq367 X0
       grind)
    | exact superpose eq367 eq2173
    | exact resolve eq2173 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2173
  have eq2205 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X1) (M.op X0 X0)) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2191 X0 X1
       have i₂ := eq343 X0
       grind)
    | exact superpose eq343 eq2191
    | exact resolve eq2191 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq2191
  have eq12735 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X0) X0)) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq392 (M.op (M.op X1 X1) (M.op (M.op X0 X0) X0)) X0
       have i₂ := eq99 X0 X1
       grind)
    | exact superpose eq99 eq392
    | exact resolve eq392 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq23895 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq99 X0 X1
       have i₂ := eq12735 X0 X1
       grind)
    | exact superpose eq12735 eq99
    | exact resolve eq99 eq12735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq12735
  have eq24005 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23895 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq23895 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq23895
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq23895 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24160 : ∀ X0 X1 : G, (σ X1) = (M.op (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23895 (σ X0) (σ X1)
       have i₂ := eq324 X0 X1
       grind)
    | exact superpose eq324 eq23895
    | (have j1 := eq324 X0 X1
       grind)
    | exact resolve eq23895 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324 eq23895
  have eq24276 : ∀ X0 X1 : G, (σ X1) = (M.op (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24160 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24160
    | (have j0 := eq24160 X0 X1
       grind)
    | exact resolve eq24160 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24160
  have eq24401 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24005 X0 X1
       have i₂ := eq2205 X0 X0
       grind)
    | exact superpose eq2205 eq24005
    | (have j0 := eq24005 X0 X1
       grind)
    | exact resolve eq24005 eq2205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24005
  have eq24435 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24276 X0 X1
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq24276
    | (have j0 := eq24276 X0 X1
       grind)
    | exact resolve eq24276 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24276
  have eq24513 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24401 X0 X1
       have i₂ := eq367 X0
       grind)
    | exact superpose eq367 eq24401
    | (have j0 := eq24401 X0 X1
       grind)
    | exact resolve eq24401 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367 eq24401
  have eq24514 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq24513 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24513
  have eq24530 : ∀ X0 X1 : G, (σ X1) = (σ (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24435 X0 X1
       have i₂ := eq104 (M.op X0 X0)
       grind)
    | exact superpose eq104 eq24435
    | (have j0 := eq24435 X0 X1
       grind)
    | exact resolve eq24435 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq24435
  have eq24580 : ∀ X0 X1 : G, (σ X1) = (σ (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24530 X0 X1
       have i₂ := eq2205 X0 X0
       grind)
    | exact superpose eq2205 eq24530
    | (have j0 := eq24530 X0 X1
       grind)
    | exact resolve eq24530 eq2205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2205 eq24530
  have eq24589 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24580 X0 X1
       have i₂ := eq359 X0
       grind)
    | exact superpose eq359 eq24580
    | (have j0 := eq24580 X0 X1
       grind)
    | exact resolve eq24580 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359 eq24580
  have eq24590 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq24589 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24589
  have eq24610 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq24514 X0 (τ X1)
       grind)
    | exact superpose eq24514 eq19
    | (have j1 := eq24514 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq24514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq24514
  have eq25016 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24610 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24610
    | exact resolve eq24610 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24610
  have eq25255 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25016 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq25016
    | (have j0 := eq25016 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq25016 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25016
  have eq26034 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24590 x y
       grind)
    | exact superpose eq24590 eq16
    | (have j1 := eq24590 x y
       grind)
    | exact resolve eq16 eq24590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24590
  have eq26093 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq26034
       have i₂ := eq25255 y x
       grind)
    | exact superpose eq25255 eq26034
    | (have j1 := eq25255 (σ x) (σ y)
       grind)
    | (have r₁ := eq26034
       have r₂ := eq25255 y x
       grind)
    | (have r₁ := eq26034
       have r₂ := eq25255 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq26034
       have r₂ := eq25255 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq26034 eq25255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25255 eq26034
  have eq26094 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq26093
  have eq26101 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq26094
       grind)
    | exact superpose eq26094 eq10
    | exact resolve eq10 eq26094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26094
  have eq26244 : x = y ∨ x = y := by
    first
    | (have i₁ := eq26101
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq26101
    | exact resolve eq26101 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26101
  have eq26245 : x = y := by grind
  clear eq26244
  have eq26264 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26245
       grind)
    | exact superpose eq26245 eq16
    | exact resolve eq16 eq26245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26245
  have eq26265 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq26264
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq26264
    | (have r₁ := eq26264
       have r₂ := eq22 x
       grind)
    | exact resolve eq26264 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq26264
  have eq26266 : False := by grind
  exact eq26266

/-- `Equation2659`: `x = ((x ◇ y) ◇ (x ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxy_pyx_pxy_pyx_pxy_Equation2659 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2659 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2659.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
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
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq33 (σ X0)
       grind)
    | exact superpose eq33 eq15
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq35
    | exact resolve eq35 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq35
  have eq80 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq92 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq252 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq92 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq13
    | (have j1 := eq92 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq92 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq92 X0 X1
       grind)
    | exact resolve eq13 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq92 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq92 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq92 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq92 X0 X0
       grind)
    | exact resolve eq12 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq259 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq252 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq263 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq254 X0 X1
       have j1 := eq80 X0 (σ X1)
       grind)
    | (have r₁ := eq254 X0 X1
       have r₂ := eq80 X0 (σ X1)
       grind)
    | exact resolve eq254 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq265 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq259 X0 X1
       have j1 := eq80 X0 (σ X1)
       grind)
    | (have r₁ := eq259 X0 X1
       have r₂ := eq80 X0 (σ X1)
       grind)
    | exact resolve eq259 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq259
  have eq281 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq263 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq263
    | (have j0 := eq263 X0 X1
       grind)
    | exact resolve eq263 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq283 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq265 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq265
    | (have j0 := eq265 X0 X1
       grind)
    | exact resolve eq265 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq284 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq283 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq295 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq281 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq281
    | (have j0 := eq281 X0 X1
       grind)
    | exact resolve eq281 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq296 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq295 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq297 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq284 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq284
    | (have j0 := eq284 X0 X1
       grind)
    | exact resolve eq284 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq284
  have eq305 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq297 X0 X1
       have j1 := eq296 X0 X1
       grind)
    | (have r₁ := eq297 X0 X1
       have r₂ := eq296 X0 X1
       grind)
    | exact resolve eq297 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296 eq297
  have eq307 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq305 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq305
    | exact resolve eq305 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq305 x y
       grind)
    | exact superpose eq305 eq16
    | exact resolve eq16 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq411 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq307 X0 (τ X1)
       grind)
    | exact superpose eq307 eq18
    | exact resolve eq18 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq307
  have eq429 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq411 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq411
    | exact resolve eq411 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq438 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq429 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq429
    | exact resolve eq429 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq458 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq319
       have i₂ := eq438 x y
       grind)
    | exact superpose eq438 eq319
    | exact resolve eq319 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319 eq438
  have eq459 : False := by grind
  exact eq459

/-- `Equation2659`: `x = ((x ◇ y) ◇ (x ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_pxy_pxy_pxx_pxy_Equation2659 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2659 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2659.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq54 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq54 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq55 (σ X0)
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq55 (τ X0)
       grind)
    | exact superpose eq55 eq18
    | exact resolve eq18 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq57
    | exact resolve eq57 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq63
    | exact resolve eq63 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq63
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq87
    | (have j0 := eq87 X0 X1
       grind)
    | exact resolve eq87 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq202 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq93
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq230 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq202 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq202
    | (have j0 := eq202 X0 X1
       grind)
    | exact resolve eq202 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq202
  have eq235 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq230 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq230 X0 (M.op (τ X0) (τ X0))
       have r₂ := eq12 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | (have r₁ := eq230 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq230 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq238 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq235 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq235
    | (have j0 := eq235 X0 X1
       grind)
    | exact resolve eq235 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq235
  have eq525 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq238 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq238
    | exact resolve eq238 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq238 (σ X0) X1
       grind)
    | exact superpose eq238 eq15
    | (have j1 := eq238 (σ X0) X1
       grind)
    | exact resolve eq15 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq554 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq539 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq539
    | (have j0 := eq539 X0 X1
       grind)
    | exact resolve eq539 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq589 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq525 (τ X1) X0
       grind)
    | exact superpose eq525 eq18
    | (have j1 := eq525 (τ X1) X0
       grind)
    | exact resolve eq18 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq594 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq525 X1 (σ X0)
       grind)
    | exact superpose eq525 eq29
    | (have j1 := eq525 X1 (σ X0)
       grind)
    | exact resolve eq29 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq525
  have eq609 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq594 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq594
    | (have j0 := eq594 X0 X1
       grind)
    | exact resolve eq594 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq2120 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq589 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq589
    | exact resolve eq589 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq2186 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2120 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2120
    | (have j0 := eq2120 X0 X1
       grind)
    | exact resolve eq2120 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2120
  have eq6435 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq554 x y
       grind)
    | exact superpose eq554 eq16
    | (have j1 := eq554 x y
       grind)
    | exact resolve eq16 eq554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6486 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq554 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq6535 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq6435
       have i₂ := eq2186 y x
       grind)
    | exact superpose eq2186 eq6435
    | (have j1 := eq2186 y x
       grind)
    | (have r₁ := eq6435
       have r₂ := eq2186 y x
       grind)
    | exact resolve eq6435 eq2186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6435
  have eq6536 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6535
  have eq6679 : y ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq6536
       grind)
    | exact superpose eq6536 eq12
    | exact resolve eq12 eq6536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6680 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq6536
       grind)
    | exact superpose eq6536 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq6536
       grind)
    | exact resolve eq13 eq6536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6536
  have eq6687 : (k x y) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6680
  have eq6688 : (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq6679
       have r₂ := eq6687
       grind)
    | exact resolve eq6679 eq6687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6679 eq6687
  have eq6694 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq220 x y
       have i₂ := eq6688
       grind)
    | exact superpose eq6688 eq220
    | (have j0 := eq220 x y
       grind)
    | exact resolve eq220 eq6688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq6710 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6694
  have eq6711 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6710
  have eq6871 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq609 x (σ y)
       have i₂ := eq6711
       grind)
    | exact superpose eq6711 eq609
    | (have j0 := eq609 x (σ y)
       grind)
    | exact resolve eq609 eq6711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq6877 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq6711
       grind)
    | exact superpose eq6711 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq6711
       grind)
    | exact resolve eq12 eq6711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6884 : (σ y) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6711
  have eq6885 : (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6877
  have eq6892 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq6885
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq6885
    | exact resolve eq6885 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6885
  have eq6895 : (τ (σ y)) = (k x (τ (σ y))) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq6871
       have r₂ := eq6884
       grind)
    | exact resolve eq6871 eq6884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6871
  have eq6900 : y = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6895
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq6895
    | exact resolve eq6895 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6895
  have eq6906 : y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6688
       have i₂ := eq6900
       grind)
    | exact superpose eq6900 eq6688
    | exact resolve eq6688 eq6900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6900
  have eq6931 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq6906
  have eq7006 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq6931
       grind)
    | exact superpose eq6931 eq12
    | exact resolve eq12 eq6931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7007 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq6931
       grind)
    | exact superpose eq6931 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq6931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6931
  have eq7020 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq7007
       have r₂ := eq66 x
       grind)
    | exact resolve eq7007 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7007
  have eq7021 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) ≠ (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7006
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq7006
    | exact resolve eq7006 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7006
  have eq7032 : (σ (k x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7020
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq7020
    | exact resolve eq7020 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7020
  have eq7042 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7032
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq7032
    | exact resolve eq7032 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7032
  have eq7043 : y = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq7042
       have r₂ := eq7021
       grind)
    | exact resolve eq7042 eq7021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7021 eq7042
  have eq7389 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6884
       have i₂ := eq7043
       grind)
    | exact superpose eq7043 eq6884
    | exact resolve eq6884 eq7043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6884 eq7043
  have eq7390 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq7389
  have eq7400 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq6892
       grind)
    | exact superpose eq6892 eq12
    | exact resolve eq12 eq6892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7401 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq6892
       grind)
    | exact superpose eq6892 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq6892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6892
  have eq7414 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq7401
       have r₂ := eq66 x
       grind)
    | exact resolve eq7401 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7401
  have eq7415 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq7400
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq7400
    | exact resolve eq7400 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7400
  have eq7426 : (σ (k x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq7414
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq7414
    | exact resolve eq7414 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7414
  have eq7436 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq7426
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq7426
    | exact resolve eq7426 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq7426
  have eq7437 : (σ y) = (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq7436
       have r₂ := eq7415
       grind)
    | exact resolve eq7436 eq7415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7415 eq7436
  have eq7673 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq7437
  have eq8376 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6486 x y
       have i₂ := eq6688
       grind)
    | exact superpose eq6688 eq6486
    | (have j0 := eq6486 x y
       grind)
    | exact resolve eq6486 eq6688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6486 eq6688
  have eq8403 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq8376
  have eq8404 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq8403
  have eq8489 : (σ y) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq7390
       have i₂ := eq8404
       grind)
    | exact superpose eq8404 eq7390
    | exact resolve eq7390 eq8404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7390
  have eq8490 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8404
       grind)
    | exact superpose eq8404 eq16
    | exact resolve eq16 eq8404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8404
  have eq8518 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq8489
       have r₂ := eq7673
       grind)
    | exact resolve eq8489 eq7673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7673 eq8489
  have eq8658 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2186 y x
       have i₂ := eq8518
       grind)
    | exact superpose eq8518 eq2186
    | (have j0 := eq2186 y x
       grind)
    | exact resolve eq2186 eq8518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2186 eq8518
  have eq8738 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq8658
       have r₂ := eq8490
       grind)
    | exact resolve eq8658 eq8490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8658
  have eq8874 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq8490
       have i₂ := eq8738
       grind)
    | exact superpose eq8738 eq8490
    | exact resolve eq8490 eq8738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8490 eq8738
  have eq8887 : False := by grind
  exact eq8887

/-- `Equation2659`: `x = ((x ◇ y) ◇ (x ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pxy_pxy_pxx_pxy_Equation2659 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2659 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2659.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 := by
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
  have eq264 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq264 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq264 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq264 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq276 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq265 (σ X0)
       grind)
    | exact superpose eq265 eq15
    | exact resolve eq15 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq265 (τ X0)
       grind)
    | exact superpose eq265 eq31
    | exact resolve eq31 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq282 X0
       have i₂ := eq265 X0
       grind)
    | exact superpose eq265 eq282
    | exact resolve eq282 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq295 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq276 X0
       have i₂ := eq265 X0
       grind)
    | exact superpose eq265 eq276
    | exact resolve eq276 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq276
  have eq504 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq527 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq504 X0 X1
       have i₂ := eq295 X0
       grind)
    | exact superpose eq295 eq504
    | (have j0 := eq504 X0 X1
       grind)
    | exact resolve eq504 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq683 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq527 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq527
    | exact resolve eq527 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq730 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq683 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq683
    | (have j0 := eq683 X0 X1
       grind)
    | exact resolve eq683 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq683
  have eq735 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq730 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq730 X1 (M.op (τ X1) (τ X1))
       have r₂ := eq12 (σ (M.op (τ X1) (τ X1))) X1
       grind)
    | (have r₁ := eq730 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq730 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq738 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq735 X0 X1
       have i₂ := eq289 X0
       grind)
    | exact superpose eq289 eq735
    | (have j0 := eq735 X0 X1
       grind)
    | exact resolve eq735 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq740 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq738 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq738
    | (have j0 := eq738 X0 X1
       grind)
    | exact resolve eq738 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq741 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq740 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq740
    | exact resolve eq740 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq753 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq740 (σ X0) X1
       grind)
    | exact superpose eq740 eq15
    | (have j1 := eq740 (σ X0) X1
       grind)
    | exact resolve eq15 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq776 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq753 X0 X1
       have i₂ := eq295 X0
       grind)
    | exact superpose eq295 eq753
    | (have j0 := eq753 X0 X1
       grind)
    | exact resolve eq753 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq794 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq741 (τ X1) X0
       grind)
    | exact superpose eq741 eq18
    | (have j1 := eq741 (τ X1) X0
       grind)
    | exact resolve eq18 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq741
  have eq952 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq794 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq794
    | exact resolve eq794 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq1005 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq952 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq952
    | (have j0 := eq952 X0 X1
       grind)
    | exact resolve eq952 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq2684 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq776 x y
       grind)
    | exact superpose eq776 eq16
    | (have j1 := eq776 x y
       grind)
    | exact resolve eq16 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2704 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq776 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq2741 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2684
       have i₂ := eq1005 y x
       grind)
    | exact superpose eq1005 eq2684
    | (have j1 := eq1005 y x
       grind)
    | (have r₁ := eq2684
       have r₂ := eq1005 y x
       grind)
    | exact resolve eq2684 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005 eq2684
  have eq2742 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2741
  have eq2746 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op y x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2742
       grind)
    | exact superpose eq2742 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2742
       grind)
    | exact resolve eq13 eq2742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2749 : x = (M.op y x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2746
  have eq2759 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2704 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq2704
    | (have j0 := eq2704 (τ X0) (τ X1)
       grind)
    | exact resolve eq2704 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2804 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (τ (M.op X0 X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2759 X0 X1
       have i₂ := eq289 X0
       grind)
    | exact superpose eq289 eq2759
    | (have j0 := eq2759 X0 X1
       grind)
    | exact resolve eq2759 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2759
  have eq2824 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2804 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq2804
    | (have j0 := eq2804 X0 X1
       grind)
    | exact resolve eq2804 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2804
  have eq2840 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2824 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2824
    | (have j0 := eq2824 X0 X1
       grind)
    | exact resolve eq2824 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2824
  have eq2852 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2840 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2840
    | (have j0 := eq2840 X0 X1
       grind)
    | exact resolve eq2840 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2840
  have eq2859 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2852 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2852
    | (have j0 := eq2852 X0 X1
       grind)
    | exact resolve eq2852 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2852
  have eq2864 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2859 X0 X1
       have i₂ := eq289 X0
       grind)
    | exact superpose eq289 eq2859
    | (have j0 := eq2859 X0 X1
       grind)
    | exact resolve eq2859 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq2859
  have eq2865 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2864 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq2864
    | (have j0 := eq2864 X0 X1
       grind)
    | exact resolve eq2864 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2864
  have eq9701 : x ≠ x ∨ (M.op x y) = (k x y) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq2749
       grind)
    | exact superpose eq2749 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq2749
       grind)
    | exact resolve eq12 eq2749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2749
  have eq9703 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
  clear eq9701
  have eq42329 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9703
       grind)
    | exact superpose eq9703 eq16
    | exact resolve eq16 eq9703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9703
  have eq42375 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq42329
       have i₂ := eq2742
       grind)
    | exact superpose eq2742 eq42329
    | exact resolve eq42329 eq2742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2742 eq42329
  have eq42400 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq42375
  have eq42401 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by grind
  clear eq42400
  have eq42427 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq42401
       grind)
    | exact superpose eq42401 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq42401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42447 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq42427
       have r₂ := eq295 x
       grind)
    | exact resolve eq42427 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42427
  have eq42453 : (σ (k x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq42447
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq42447
    | exact resolve eq42447 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42447
  have eq42457 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq42453
       have i₂ := eq295 x
       grind)
    | exact superpose eq295 eq42453
    | exact resolve eq42453 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq42453
  have eq74504 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq42457
       grind)
    | exact superpose eq42457 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq42457
       grind)
    | exact resolve eq12 eq42457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42457
  have eq74516 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by grind
  clear eq74504
  have eq74528 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq74516
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq74516
    | exact resolve eq74516 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74516
  have eq848489 : (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq42401
       have i₂ := eq74528
       grind)
    | exact superpose eq74528 eq42401
    | exact resolve eq42401 eq74528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42401 eq74528
  have eq848735 : (k x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq848489
  have eq849135 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2704 x y
       have i₂ := eq848735
       grind)
    | exact superpose eq848735 eq2704
    | (have j0 := eq2704 x y
       grind)
    | (have r₁ := eq2704 x y
       have r₂ := eq848735
       grind)
    | exact resolve eq2704 eq848735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq849137 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2865 x y
       have i₂ := eq848735
       grind)
    | exact superpose eq848735 eq2865
    | (have j0 := eq2865 x y
       grind)
    | (have r₁ := eq2865 x y
       have r₂ := eq848735
       grind)
    | exact resolve eq2865 eq848735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848735
  have eq849361 : (M.op x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq849137
  have eq849363 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq849135
  have eq849370 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq2704 x y
       grind)
    | (have r₁ := eq849363
       have r₂ := eq2704 x y
       grind)
    | exact resolve eq849363 eq2704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2704 eq849363
  have eq849415 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq849370
       grind)
    | exact superpose eq849370 eq16
    | exact resolve eq16 eq849370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849370
  have eq849845 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq849415
       have i₂ := eq849361
       grind)
    | exact superpose eq849361 eq849415
    | exact resolve eq849415 eq849361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849361
  have eq849860 : (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq849845
  have eq849997 : (k x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq849860
       grind)
    | exact superpose eq849860 eq10
    | exact resolve eq10 eq849860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849860
  have eq850660 : (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq849997
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq849997
    | exact resolve eq849997 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849997
  have eq851269 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2865 x y
       have i₂ := eq850660
       grind)
    | exact superpose eq850660 eq2865
    | (have j0 := eq2865 x y
       grind)
    | (have r₁ := eq2865 x y
       have r₂ := eq850660
       grind)
    | exact resolve eq2865 eq850660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2865 eq850660
  have eq851493 : (M.op x y) = (M.op x x) := by grind
  clear eq851269
  have eq851602 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq849415
       have i₂ := eq851493
       grind)
    | exact superpose eq851493 eq849415
    | exact resolve eq849415 eq851493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849415 eq851493
  have eq851617 : False := by grind
  exact eq851617
