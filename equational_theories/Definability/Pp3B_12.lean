import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pyx_x_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) := by
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
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq14 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
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
  have eq64 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ X0 ∨ (k (M.op (M.op X0 X2) X0) (M.op X1 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 X2) X0) (M.op X1 X1)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 (M.op (M.op (M.op X1 X1) X2) (M.op X1 X1)) (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq82 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq85 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq89 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq97 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq89
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq99
    | exact resolve eq99 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq104 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq76
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq104
  have eq211 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 X0) x) := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq53 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X1 X2)) = (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (M.op X1 X2) X3 X1
       have i₂ := eq53 X1 X0 X2
       grind)
    | (have i₁ := eq53 (M.op X1 X1) X1 X0
       have i₂ := eq53 X0 X1 X2
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq53 X1 X3 x
       have i₂ := eq53 X1 X0 x
       grind)
    | (have i₁ := eq53 X0 X1 X0
       have i₂ := eq53 X0 X0 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 x X2
       have i₂ := eq53 X0 x X1
       grind)
    | (have i₁ := eq53 X2 X2 X2
       have i₂ := eq53 X2 X1 X2
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) x) X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq215 eq53
    | exact resolve eq53 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 x
       have i₂ := eq53 X1 X0 x
       grind)
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq53 X0 X0 X2
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq634 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq65 (M.op X0 X0) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq932 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq373 sF0
       have i₂ := eq371 sF0 x x
       grind)
    | (have i₁ := eq373 sF0
       have i₂ := eq371 sF0 x x
       grind)
    | exact superpose eq371 eq373
    | exact resolve eq373 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq950 : ∀ X0 X1 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op (M.op X1 X1) (M.op (M.op (M.op x y) x) X0)) := by
    intro X0 X1
    first
    | exact superpose eq373 eq53
    | exact resolve eq53 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq954 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq374 sF4
       have i₂ := eq371 sF4 x sF2
       grind)
    | (have i₁ := eq374 sF4
       have i₂ := eq371 sF4 sF2 x
       grind)
    | exact superpose eq371 eq374
    | exact resolve eq374 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq1051 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq358 X3 X1 x
       have i₂ := eq358 X0 X1 x
       grind)
    | (have i₁ := eq358 X0 X1 X3
       have i₂ := eq358 (M.op X3 X3) X1 X3
       grind)
    | exact superpose eq358 eq358
    | exact resolve eq358 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1062 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X1))) = (M.op (M.op X2 X2) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq358 X0 (M.op X1 X1) X3
       have i₂ := eq358 X0 X1 X1
       grind)
    | (have i₁ := eq358 X0 (M.op X1 X1) X3
       have i₂ := eq358 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq358 eq358
    | exact resolve eq358 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1088 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X2 X3) X2)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) X3
       have i₂ := eq358 X0 X1 X1
       grind)
    | (have i₁ := eq14 X0 (M.op X1 X1) X2
       have i₂ := eq358 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq358 eq14
    | exact resolve eq14 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1089 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op X1 X1)
       have i₂ := eq358 X0 X1 X1
       grind)
    | (have i₁ := eq50 (M.op X1 X1)
       have i₂ := eq358 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq358 eq50
    | exact resolve eq50 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1090 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X1)
       have i₂ := eq358 X0 X1 X1
       grind)
    | (have i₁ := eq51 (M.op X1 X1)
       have i₂ := eq358 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq358 eq51
    | exact resolve eq51 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1093 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X2 (M.op X1 X1) X3
       have i₂ := eq358 X0 X1 X1
       grind)
    | (have i₁ := eq53 X0 (M.op X1 X1) X2
       have i₂ := eq358 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq358 eq53
    | exact resolve eq53 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1096 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op X1 X1)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq211 (M.op X1 X1)
       have i₂ := eq358 X0 X1 X1
       grind)
    | (have i₁ := eq211 (M.op X1 X1)
       have i₂ := eq358 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq358 eq211
    | exact resolve eq211 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1097 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 (M.op X1 X1)) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq215 (M.op X1 X1)
       have i₂ := eq358 X0 X1 X1
       grind)
    | (have i₁ := eq215 (M.op X1 X1)
       have i₂ := eq358 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq358 eq215
    | exact resolve eq215 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq1098 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) X2) = (M.op (M.op X3 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq370 (M.op X1 X1) X2 X3
       have i₂ := eq358 X0 X1 X1
       grind)
    | (have i₁ := eq370 (M.op X1 X1) X1 X3
       have i₂ := eq358 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq358 eq370
    | exact resolve eq370 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq1145 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1062 X0 X1 x X3
       have i₂ := eq52 X0 x X1
       grind)
    | exact superpose eq52 eq1062
    | exact resolve eq1062 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1062
  have eq1162 : ∀ X0 X1 : G, (M.op x (M.op (M.op (M.op x y) X0) (M.op x y))) = (M.op (M.op X1 X1) (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq932 eq53
    | exact resolve eq53 eq932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932
  have eq1166 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1162 x x
       have i₂ := eq14 sF0 x x
       grind)
    | exact superpose eq14 eq1162
    | exact resolve eq1162 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq1238 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y)))) = (M.op (M.op X1 X1) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq954 eq53
    | exact resolve eq53 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq1242 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1238 x x
       have i₂ := eq14 sF4 x x
       grind)
    | exact superpose eq14 eq1238
    | exact resolve eq1238 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238
  have eq1392 : ∀ X0 X1 : G, (M.op x y) = (M.op x (M.op (M.op X0 (M.op X1 X1)) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1166 (M.op X1 X1)
       have i₂ := eq1051 sF0 X1 x
       grind)
    | (have i₁ := eq1166 (M.op X1 X1)
       have i₂ := eq1051 X0 X1 sF0
       grind)
    | exact superpose eq1051 eq1166
    | exact resolve eq1166 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166
  have eq1395 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op X0 (M.op X1 X1)) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1242 (M.op X1 X1)
       have i₂ := eq1051 sF4 X1 x
       grind)
    | (have i₁ := eq1242 (M.op X1 X1)
       have i₂ := eq1051 X0 X1 sF4
       grind)
    | exact superpose eq1051 eq1242
    | exact resolve eq1242 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242
  have eq3386 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X4 X4) X2) (M.op X2 X3)) = (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq363 X4 X2 X3 (M.op X1 X1)
       have i₂ := eq358 X0 X1 X1
       grind)
    | (have i₁ := eq363 X0 X1 X2 (M.op X1 X1)
       have i₂ := eq358 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq358 eq363
    | exact resolve eq363 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3474 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op X4 X4) (M.op X0 X3)) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq363 X0 (M.op X0 X2) X0 X3
       have i₂ := eq371 X0 X1 X2
       grind)
    | (have i₁ := eq363 X0 (M.op X0 X1) X0 X3
       have i₂ := eq371 X0 X1 X2
       grind)
    | exact superpose eq371 eq363
    | exact resolve eq363 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq3480 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) x) = (M.op (M.op (M.op X2 X2) (M.op (M.op (M.op x y) x) X1)) x) := by
    intro X0 X1 X2
    first
    | exact superpose eq373 eq363
    | exact resolve eq363 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363 eq373
  have eq3707 : ∀ X1 X2 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op X2 X2) (M.op (M.op (M.op x y) x) X1)) x) := by
    intro X1 X2
    first
    | (have i₁ := eq3480 x X1 X2
       have i₂ := eq211 x
       grind)
    | exact superpose eq211 eq3480
    | exact resolve eq3480 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq3480
  have eq3713 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op X4 X4) (M.op X0 X3)) (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq3474 X0 X1 x X3 X4
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq3474
    | exact resolve eq3474 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3474
  have eq4370 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (k (M.op (M.op (M.op X0 (M.op X1 X1)) X2) (M.op X0 (M.op X1 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq634 (M.op X1 X1) X1
       have i₂ := eq358 X0 X1 X1
       grind)
    | (have i₁ := eq634 (M.op X1 X1) X1
       have i₂ := eq358 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq358 eq634
    | exact resolve eq634 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq4385 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4370 X0 X1 x
       have i₂ := eq1145 X0 X1 (M.op (M.op X0 (M.op X1 X1)) x)
       grind)
    | exact superpose eq1145 eq4370
    | exact resolve eq4370 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4370
  have eq5553 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq84 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq84
    | (have j0 := eq84 x
       grind)
    | exact resolve eq84 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq5572 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5553
  have eq5583 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5572
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq5572
    | exact resolve eq5572 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq5572
  have eq5601 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq5583
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq5583 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5583
  have eq5607 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5601 eq49
    | exact resolve eq49 eq5601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq5726 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq85 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq85
    | (have j0 := eq85 y
       grind)
    | exact resolve eq85 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq5743 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5726
  have eq5748 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5743
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq5743
    | exact resolve eq5743 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq5743
  have eq5772 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq5748
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq5748 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5748
  have eq5793 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq5772 eq109
    | exact resolve eq109 eq5772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq12874 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq5601 eq97
    | exact resolve eq97 eq5601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq5601
  have eq12951 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq12952 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq12951
    | exact resolve eq12951 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12951
  have eq12963 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq12952
       have r₂ := eq27
       grind)
    | exact resolve eq12952 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12952
  have eq12965 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq12963
    | exact resolve eq12963 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12963
  have eq12967 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq12965 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq12965
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq12965
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq12965
       grind)
    | exact resolve eq12 eq12965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12965
  have eq12980 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq12967
  have eq12981 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq12980
    | exact resolve eq12980 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12980
  have eq12982 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq12981
  have eq13181 : (σ (M.op y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq5772 eq110
    | exact resolve eq110 eq5772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq5772
  have eq13329 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq12982 eq82
    | exact resolve eq82 eq12982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12982
  have eq13349 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq13329
    | exact resolve eq13329 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13329
  have eq13990 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq13349
       grind)
    | exact superpose eq13349 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq13349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13349
  have eq13991 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13990
  have eq13994 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13991
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13991
    | exact resolve eq13991 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13991
  have eq13995 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13994
  have eq14147 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq13995
       grind)
    | exact superpose eq13995 eq14
    | exact resolve eq14 eq13995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14513 : x = (M.op y (M.op (M.op x y) x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1089 (M.op x x) y
       have i₂ := eq14147 x
       grind)
    | exact superpose eq14147 eq1089
    | exact resolve eq1089 eq14147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089
  have eq14515 : (M.op (M.op x y) x) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1096 (M.op x x) y
       have i₂ := eq14147 x
       grind)
    | exact superpose eq14147 eq1096
    | exact resolve eq1096 eq14147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14558 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1051 X0 (M.op y y) x
       have i₂ := eq14147 y
       grind)
    | exact superpose eq14147 eq1051
    | exact resolve eq1051 eq14147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14147
  have eq14762 : x = (M.op y (M.op y x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14515 eq14513
    | exact resolve eq14513 eq14515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14513 eq14515
  have eq14777 : x = (M.op y (M.op y x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14762
  have eq14958 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14558 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14558
    | (have j0 := eq14558 x X0
       grind)
    | exact resolve eq14558 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14558
  have eq15554 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14777
       have i₂ := eq13995
       grind)
    | exact superpose eq13995 eq14777
    | exact resolve eq14777 eq13995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13995 eq14777
  have eq15572 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15554
  have eq15585 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14958 y
       have i₂ := eq15572
       grind)
    | exact superpose eq15572 eq14958
    | exact resolve eq14958 eq15572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14958 eq15572
  have eq15650 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15585
  have eq15670 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15650 eq64
    | (have r₁ := eq64
       have r₂ := eq15650
       grind)
    | exact resolve eq64 eq15650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq15679 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (M.op (M.op X0 (M.op X1 X1)) (σ x))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq15650 eq1395
    | exact resolve eq1395 eq15650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395
  have eq15685 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq15670
  have eq15688 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1097 eq15679
    | exact resolve eq15679 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15679
  have eq15808 : (τ (σ x)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15685 eq82
    | exact resolve eq82 eq15685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq15685
  have eq15838 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq15808
    | exact resolve eq15808 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15808
  have eq15861 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq15838
       grind)
    | exact superpose eq15838 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq15838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15870 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15861
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15861
    | exact resolve eq15861 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15861
  have eq15871 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq15870
  have eq16016 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15650 eq15688
    | exact resolve eq15688 eq15650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15688
  have eq16035 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq16016
  have eq16190 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16035
       have i₂ := eq1051 sF2 sF2 x
       grind)
    | (have i₁ := eq16035
       have i₂ := eq1051 X0 sF2 sF2
       grind)
    | exact superpose eq1051 eq16035
    | exact resolve eq16035 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16200 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16035 eq1145
    | exact resolve eq1145 eq16035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16395 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op X1 (σ x))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq16190 eq1145
    | exact resolve eq1145 eq16190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16729 : ∀ X0 : G, (k x x) = (τ (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16200 eq5607
    | exact resolve eq5607 eq16200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16200
  have eq18506 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq16035 eq1088
    | exact resolve eq1088 eq16035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16035
  have eq19280 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16190 eq18506
    | exact resolve eq18506 eq16190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16190 eq18506
  have eq19491 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq19280 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19280
  have eq19520 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq19491
    | (have j0 := eq19491 (σ y)
       grind)
    | exact resolve eq19491 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19491
  have eq20214 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15650 eq19520
    | exact resolve eq19520 eq15650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15650 eq19520
  have eq20237 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq20214
  have eq20299 : (τ (σ y)) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20237 eq16729
    | exact resolve eq16729 eq20237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16729
  have eq20301 : ∀ X0 : G, (σ x) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20237 eq16395
    | exact resolve eq16395 eq20237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16395 eq20237
  have eq20370 : ∀ X0 : G, (σ x) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq20301 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20301
  have eq20372 : (τ (σ y)) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq20299
  have eq20384 : y = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq20372
    | exact resolve eq20372 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq20372
  have eq21026 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20370 eq5793
    | exact resolve eq5793 eq20370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20370
  have eq21035 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq21026
    | exact resolve eq21026 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq21026
  have eq23523 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq12874
       grind)
    | exact superpose eq12874 eq16
    | exact resolve eq16 eq12874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23574 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq5607 eq23523
    | exact resolve eq23523 eq5607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5607 eq23523
  have eq23578 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq23574
       have r₂ := eq13 x x
       grind)
    | exact resolve eq23574 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23574
  have eq23908 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq13181
       grind)
    | exact superpose eq13181 eq16
    | exact resolve eq16 eq13181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23961 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq5793 eq23908
    | exact resolve eq23908 eq5793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23908
  have eq23965 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq23961
       have r₂ := eq13 y y
       grind)
    | exact resolve eq23961 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23961
  have eq154161 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X3)) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (M.op (M.op X0 X0) (M.op (σ x) X1)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq376 eq3386
    | exact resolve eq3386 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376 eq3386
  have eq155257 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 X0) (M.op (σ x) X1)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq1090 eq154161
    | exact resolve eq154161 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090 eq154161
  have eq282254 : y ≠ y ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq15871
       grind)
    | exact superpose eq15871 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq15871
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq15871
       grind)
    | exact resolve eq12 eq15871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282304 : x ≠ y ∨ x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq15871
  have eq282312 : x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq282254
  have eq282319 : x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq282312
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq282312
    | exact resolve eq282312 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282312
  have eq282320 : y = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq282319
  have eq289333 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq15838
       have i₂ := eq282320
       grind)
    | exact superpose eq282320 eq15838
    | exact resolve eq15838 eq282320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15838 eq282320
  have eq289351 : x = y ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq289333
  have eq289366 : x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq289351
       have r₂ := eq282304
       grind)
    | exact resolve eq289351 eq282304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282304 eq289351
  have eq289401 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 X0) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq53 y X0 x
       have i₂ := eq289366
       grind)
    | exact superpose eq289366 eq53
    | exact resolve eq53 eq289366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq289366
  have eq289514 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 X0) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq289401 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq289401
    | (have j0 := eq289401 X0
       grind)
    | exact resolve eq289401 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289401
  have eq1341989 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23578
       have i₂ := eq20384
       grind)
    | exact superpose eq20384 eq23578
    | exact resolve eq23578 eq20384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20384 eq23578
  have eq1342993 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq289514 x
       have i₂ := eq1341989
       grind)
    | exact superpose eq1341989 eq289514
    | exact resolve eq289514 eq1341989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289514 eq1341989
  have eq1343145 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq1342993
  have eq1343426 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23965
       have i₂ := eq21035
       grind)
    | exact superpose eq21035 eq23965
    | exact resolve eq23965 eq21035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21035
  have eq1344619 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1343145
       have i₂ := eq1343426
       grind)
    | exact superpose eq1343426 eq1343145
    | exact resolve eq1343145 eq1343426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343145 eq1343426
  have eq1345161 : x = (M.op x y) := by grind
  clear eq1344619
  have eq1345355 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1345161 eq20
    | exact resolve eq20 eq1345161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1345359 : x ≠ x ∨ x = (k y x) := by
    first
    | exact superpose eq1345161 eq63
    | (have r₁ := eq63
       have r₂ := eq1345161
       grind)
    | exact resolve eq63 eq1345161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq1345429 : ∀ X0 X1 : G, (M.op x (M.op (M.op x x) X0)) = (M.op (M.op X1 X1) (M.op (M.op x x) X0)) := by
    intro X0 X1
    first
    | exact superpose eq1345161 eq950
    | exact resolve eq950 eq1345161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq1345436 : ∀ X0 X1 : G, x = (M.op x (M.op (M.op X0 (M.op X1 X1)) x)) := by
    intro X0 X1
    first
    | exact superpose eq1345161 eq1392
    | exact resolve eq1392 eq1345161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392
  have eq1345527 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op (M.op X0 X0) (M.op (M.op x x) X1)) x) := by
    intro X0 X1
    first
    | exact superpose eq1345161 eq3707
    | exact resolve eq3707 eq1345161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3707
  have eq1345605 : x = (k y x) := by grind
  clear eq1345359
  have eq1345619 : ∀ X1 : G, (M.op x x) = (M.op X1 x) := by
    intro X1
    first
    | (have i₁ := eq1345527 x X1
       have i₂ := eq378 x X1 x
       grind)
    | exact superpose eq378 eq1345527
    | exact resolve eq1345527 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345527
  have eq1345700 : x = (M.op x (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq1345436 x x
       have i₂ := eq1096 x x
       grind)
    | exact superpose eq1096 eq1345436
    | exact resolve eq1345436 eq1096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096 eq1345436
  have eq1345704 : ∀ X0 : G, (M.op x (M.op (M.op x x) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1345429 X0 x
       have i₂ := eq378 x X0 x
       grind)
    | exact superpose eq378 eq1345429
    | exact resolve eq1345429 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq1345429
  have eq1345768 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1345355
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1345355
    | exact resolve eq1345355 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345355
  have eq1345771 : x = (M.op x (M.op x x)) := by
    first
    | exact superpose eq1345161 eq1345700
    | exact resolve eq1345700 eq1345161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345700
  have eq1345815 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1345768 eq26
    | exact resolve eq26 eq1345768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1346640 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq1345605
       grind)
    | exact superpose eq1345605 eq75
    | exact resolve eq75 eq1345605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq1345605
  have eq1346819 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1345768 eq1346640
    | exact resolve eq1346640 eq1345768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346640
  have eq1346900 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1346819
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1346819
    | exact resolve eq1346819 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346819
  have eq1346980 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1345768 eq1346900
    | exact resolve eq1346900 eq1345768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346900
  have eq1347732 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1346980 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq1346980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1347774 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1345815 eq1347732
    | exact resolve eq1347732 eq1345815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347732
  have eq1347796 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq1347774
       have r₂ := eq27
       grind)
    | exact resolve eq1347774 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347774
  have eq1351115 : ∀ X0 : G, x = (M.op X0 (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq1345771
       have i₂ := eq1051 x x X0
       grind)
    | (have i₁ := eq1345771
       have i₂ := eq1051 X0 x x
       grind)
    | exact superpose eq1051 eq1345771
    | exact resolve eq1345771 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051
  have eq1351125 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1088 x x X0 X1
       have i₂ := eq1345771
       grind)
    | exact superpose eq1345771 eq1088
    | exact resolve eq1088 eq1345771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq1351128 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1093 x x X0 X1
       have i₂ := eq1345771
       grind)
    | exact superpose eq1345771 eq1093
    | exact resolve eq1093 eq1345771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq1351131 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq1097 x x
       have i₂ := eq1345771
       grind)
    | exact superpose eq1345771 eq1097
    | exact resolve eq1097 eq1345771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097
  have eq1351132 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1098 x x X0 X1
       have i₂ := eq1345771
       grind)
    | exact superpose eq1345771 eq1098
    | exact resolve eq1098 eq1345771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098 eq1345771
  have eq1351357 : (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq1345768 eq1351131
    | exact resolve eq1351131 eq1345768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351131
  have eq1368129 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1351125 X0 (M.op x x)
       have i₂ := eq1351115 X0
       grind)
    | exact superpose eq1351115 eq1351125
    | exact resolve eq1351125 eq1351115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351125
  have eq1370601 : y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1368129 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1368129
    | (have j0 := eq1368129 y
       grind)
    | exact resolve eq1368129 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1370960 : y = (M.op x x) := by
    first
    | exact superpose eq1345161 eq1370601
    | exact resolve eq1370601 eq1345161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370601
  have eq1371090 : ∀ X0 : G, y = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq1370960
       have i₂ := eq1345619 X0
       grind)
    | (have i₁ := eq1370960
       have i₂ := eq1345619 x
       grind)
    | exact superpose eq1345619 eq1370960
    | exact resolve eq1370960 eq1345619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345619
  have eq1371095 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq12874
       have i₂ := eq1370960
       grind)
    | exact superpose eq1370960 eq12874
    | exact resolve eq12874 eq1370960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12874
  have eq1371099 : ∀ X0 : G, (M.op x (M.op y X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1345704 X0
       have i₂ := eq1370960
       grind)
    | exact superpose eq1370960 eq1345704
    | exact resolve eq1345704 eq1370960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345704
  have eq1371102 : ∀ X0 : G, x = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1351115 X0
       have i₂ := eq1370960
       grind)
    | exact superpose eq1370960 eq1351115
    | exact resolve eq1351115 eq1370960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351115 eq1370960
  have eq1371786 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1345768 eq1371095
    | exact resolve eq1371095 eq1345768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371095
  have eq1371920 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq1371786
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1371786
    | exact resolve eq1371786 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371786
  have eq1374201 : ∀ X0 : G, (M.op X0 x) = (k x (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq4385 X0 y
       have i₂ := eq1371102 y
       grind)
    | exact superpose eq1371102 eq4385
    | exact resolve eq4385 eq1371102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4385
  have eq1375032 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq13181
       have i₂ := eq1371102 y
       grind)
    | exact superpose eq1371102 eq13181
    | exact resolve eq13181 eq1371102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13181 eq1371102
  have eq1375207 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1375032
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1375032
    | exact resolve eq1375032 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375032
  have eq1375414 : y = (k x y) := by
    first
    | (have i₁ := eq1374201 x
       have i₂ := eq1371090 x
       grind)
    | exact superpose eq1371090 eq1374201
    | exact resolve eq1374201 eq1371090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371090 eq1374201
  have eq1375457 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1345768 eq1375207
    | exact resolve eq1375207 eq1345768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375207
  have eq1377243 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1375414
       grind)
    | exact superpose eq1375414 eq44
    | exact resolve eq44 eq1375414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1375414
  have eq1377418 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1345768 eq1377243
    | exact resolve eq1377243 eq1345768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377243
  have eq1377497 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq1377418
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1377418
    | exact resolve eq1377418 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377418
  have eq1378156 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1377497 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq11 eq1377497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377497
  have eq1378199 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1345815 eq1378156
    | exact resolve eq1378156 eq1345815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378156
  have eq1378219 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1345815 eq1378199
    | exact resolve eq1378199 eq1345815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378199
  have eq1378239 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1378219
       have r₂ := eq27
       grind)
    | exact resolve eq1378219 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378219
  have eq1378445 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq1368129 (M.op y X0)
       have i₂ := eq1371099 X0
       grind)
    | exact superpose eq1371099 eq1368129
    | exact resolve eq1368129 eq1371099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368129 eq1371099
  have eq1401213 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1347796 eq12
    | (have j0 := eq12 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq12 (σ y) (σ (M.op x y))
       have r₂ := eq1347796
       grind)
    | exact resolve eq12 eq1347796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1401326 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq1347796
  have eq1401328 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq1401213
  have eq1401409 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1345815 eq1401328
    | exact resolve eq1401328 eq1345815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401328
  have eq1401453 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq1401409
       have r₂ := eq27
       grind)
    | exact resolve eq1401409 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401409
  have eq1401467 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1346980 eq1401453
    | exact resolve eq1401453 eq1346980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346980 eq1401453
  have eq1401481 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq1401467
       have r₂ := eq1401326
       grind)
    | exact resolve eq1401467 eq1401326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401326 eq1401467
  have eq1401622 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X0 X0) (M.op (σ y) X1)) (M.op (σ (M.op x y)) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq1401481 eq3713
    | exact resolve eq3713 eq1401481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3713
  have eq1401690 : (M.op (σ (M.op x y)) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq1401481 eq1351128
    | exact resolve eq1351128 eq1401481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351128
  have eq1401691 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq1345815 eq1401690
    | exact resolve eq1401690 eq1345815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401690
  have eq1401748 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X0 X0) (M.op (σ y) X1)) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq1345815 eq1401622
    | exact resolve eq1401622 eq1345815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345815 eq1401622
  have eq1401827 : ∀ X1 : G, (σ y) = (M.op (M.op x (M.op (σ y) X1)) (M.op (σ x) (σ y))) := by
    intro X1
    first
    | (have i₁ := eq1401748 X1 X1
       have i₂ := eq1351132 (M.op sF3 X1) X1
       grind)
    | exact superpose eq1351132 eq1401748
    | exact resolve eq1401748 eq1351132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401748
  have eq1404934 : (σ y) = (M.op (M.op x (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1378239 eq1401827
    | exact resolve eq1401827 eq1378239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378239 eq1401827
  have eq1405380 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1401691 eq1404934
    | exact resolve eq1404934 eq1401691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404934
  have eq1405691 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ y)) = (M.op X1 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1405380 eq358
    | exact resolve eq358 eq1405380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358 eq1405380
  have eq1406474 : ∀ X1 : G, (M.op X1 (σ y)) = (M.op x (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq1405691 X1 X1
       have i₂ := eq1351132 sF3 X1
       grind)
    | exact superpose eq1351132 eq1405691
    | exact resolve eq1405691 eq1351132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405691
  have eq1406655 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op X1 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq1401691 eq1406474
    | exact resolve eq1406474 eq1401691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401691 eq1406474
  have eq1408564 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1406655 eq5793
    | exact resolve eq5793 eq1406655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5793 eq1406655
  have eq1408655 : (τ (M.op (σ x) (σ y))) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1408564
       have i₂ := eq23965
       grind)
    | exact superpose eq23965 eq1408564
    | exact resolve eq1408564 eq23965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23965 eq1408564
  have eq1409122 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1408655
       have i₂ := eq1378445 y
       grind)
    | exact superpose eq1378445 eq1408655
    | exact resolve eq1408655 eq1378445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378445 eq1408655
  have eq1409331 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1409122
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1409122
    | exact resolve eq1409122 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1409122
  have eq1409428 : x = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1345161 eq1409331
    | exact resolve eq1409331 eq1345161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345161 eq1409331
  have eq1410154 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1409428 eq15
    | exact resolve eq15 eq1409428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409428
  have eq1411081 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1410154
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1410154
    | exact resolve eq1410154 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410154
  have eq1411256 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1345768 eq1411081
    | exact resolve eq1411081 eq1345768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411081
  have eq1411381 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1411256
       have r₂ := eq27
       grind)
    | exact resolve eq1411256 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411256
  have eq1411525 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq1411381 eq27
    | exact resolve eq27 eq1411381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1411987 : (M.op (σ y) (σ (M.op x y))) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq1411381 eq1351357
    | exact resolve eq1351357 eq1411381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411381
  have eq1412005 : (σ (M.op x y)) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq1401481 eq1411987
    | exact resolve eq1411987 eq1401481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401481 eq1411987
  have eq1412681 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 X0) (M.op (σ (M.op x y)) X1)) (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq1345768 eq155257
    | exact resolve eq155257 eq1345768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155257
  have eq1412682 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 X0) (M.op (σ (M.op x y)) X1)) (M.op x (σ (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq1351357 eq1412681
    | exact resolve eq1412681 eq1351357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351357 eq1412681
  have eq1412683 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 X0) (M.op (σ (M.op x y)) X1)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq1412005 eq1412682
    | exact resolve eq1412682 eq1412005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412682
  have eq1412684 : ∀ X1 : G, (σ (M.op x y)) = (M.op (M.op x (M.op (σ (M.op x y)) X1)) (σ (M.op x y))) := by
    intro X1
    first
    | (have i₁ := eq1412683 X1 X1
       have i₂ := eq1351132 (M.op sF1 X1) X1
       grind)
    | exact superpose eq1351132 eq1412683
    | exact resolve eq1412683 eq1351132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351132 eq1412683
  have eq1412724 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op x (M.op X0 X0)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1412684 (M.op X0 (M.op x x))
       have i₂ := eq1145 X0 x sF1
       grind)
    | exact superpose eq1145 eq1412684
    | exact resolve eq1412684 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145 eq1412684
  have eq1413604 : (σ (M.op x y)) = (M.op (M.op x (σ (M.op x y))) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1375457 eq1412724
    | exact resolve eq1412724 eq1375457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375457 eq1412724
  have eq1413997 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1412005 eq1413604
    | exact resolve eq1413604 eq1412005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412005 eq1413604
  have eq1414300 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1413997 eq1371920
    | exact resolve eq1371920 eq1413997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371920 eq1413997
  have eq1414864 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1414300
  have eq1415172 : x = y := by
    first
    | (have r₁ := eq1414864
       have r₂ := eq1411525
       grind)
    | exact resolve eq1414864 eq1411525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414864
  have eq1415627 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1415172
       grind)
    | exact superpose eq1415172 eq24
    | exact resolve eq24 eq1415172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1415172
  have eq1416266 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1415627
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1415627
    | exact resolve eq1415627 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1415627
  have eq1416440 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1345768 eq1416266
    | exact resolve eq1416266 eq1345768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345768 eq1416266
  have eq1416549 : False := by grind
  exact eq1416549

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pxy_pyy_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) := by
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
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq14 X0 (M.op (M.op X0 X2) X0) X2
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
  clear eq37
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq80
    | exact resolve eq80 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq88
    | exact resolve eq88 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq96 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
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
  have eq101 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq16
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq96
  have eq337 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq54 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq388 : ∀ X0 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    grind
  have eq396 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq388 X0
       have i₂ := eq53 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq53 eq388
    | exact resolve eq388 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq388
  have eq473 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq484 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq73 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq485 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq484 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq494 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq473 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq497 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq494 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq494
    | (have j0 := eq494 X0
       grind)
    | exact resolve eq494 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq1080 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq337 X3 X1 x
       have i₂ := eq337 X0 X1 x
       grind)
    | (have i₁ := eq337 X0 X1 X3
       have i₂ := eq337 (M.op X3 X3) X1 X3
       grind)
    | exact superpose eq337 eq337
    | exact resolve eq337 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq3395 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq485 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq485
    | (have j0 := eq485 (τ X0)
       grind)
    | exact resolve eq485 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3403 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3395 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3395
    | (have j0 := eq3395 X0
       grind)
    | exact resolve eq3395 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3395
  have eq3409 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3403 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3403
    | (have j0 := eq3403 X0
       grind)
    | exact resolve eq3403 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3403
  have eq5790 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq497 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq497
    | exact resolve eq497 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq5894 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (k X0 (σ (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5790 X0
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq5790
    | (have j0 := eq5790 X0
       grind)
    | exact resolve eq5790 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5790
  have eq5912 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5894 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5894
    | (have j0 := eq5894 X0
       grind)
    | exact resolve eq5894 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5894
  have eq5923 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5912 X0
       have i₂ := eq39 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq39 eq5912
    | (have j0 := eq5912 X0
       grind)
    | exact resolve eq5912 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq5912
  have eq5933 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k (k X0 (σ (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5923 X0
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq5923
    | (have j0 := eq5923 X0
       grind)
    | exact resolve eq5923 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq5923
  have eq5940 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5933 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5933
    | (have j0 := eq5933 X0
       grind)
    | exact resolve eq5933 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5933
  have eq19337 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq89 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19338 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq19337
    | exact resolve eq19337 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19337
  have eq19349 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq19338
       have r₂ := eq28
       grind)
    | exact resolve eq19338 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19338
  have eq19371 : (σ y) = (k (σ y) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19349 eq396
    | exact resolve eq396 eq19349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19409 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  have eq19515 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19349 eq19371
    | exact resolve eq19371 eq19349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19349 eq19371
  have eq19520 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq19515
  have eq19521 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq19520
       have r₂ := eq19409
       grind)
    | exact resolve eq19520 eq19409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19409 eq19520
  have eq19527 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq19521 eq101
    | exact resolve eq101 eq19521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq19521
  have eq19569 : y = (k y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq30 eq19527
    | exact resolve eq19527 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq19527
  have eq19572 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq3409 y
       grind)
    | (have r₁ := eq19569
       have r₂ := eq3409 y
       grind)
    | exact resolve eq19569 eq3409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3409 eq19569
  have eq19577 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by grind
  clear eq19572
  have eq19644 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq19577
    | exact resolve eq19577 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19577
  have eq19651 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq19644 eq89
    | exact resolve eq89 eq19644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq19644
  have eq19661 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq19651
  have eq19663 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq19661
       have r₂ := eq28
       grind)
    | exact resolve eq19661 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19661
  have eq19667 : (k y y) = (M.op y y) ∨ x = (M.op y y) := by grind
  have eq19685 : y = (k y (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq396 y
       have i₂ := eq19663
       grind)
    | exact superpose eq19663 eq396
    | exact resolve eq396 eq19663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq19692 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq1080 X0 y x
       have i₂ := eq19663
       grind)
    | exact superpose eq19663 eq1080
    | exact resolve eq1080 eq19663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19723 : x ≠ y ∨ x = (M.op y y) := by grind
  have eq19969 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq71
       have i₂ := eq19667
       grind)
    | exact superpose eq19667 eq71
    | exact resolve eq71 eq19667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq19667
  have eq20356 : y = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq19685
       have i₂ := eq19663
       grind)
    | exact superpose eq19663 eq19685
    | exact resolve eq19685 eq19663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19663 eq19685
  have eq20363 : y = (k y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq20356
       have r₂ := eq19723
       grind)
    | exact resolve eq20356 eq19723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19723 eq20356
  have eq20380 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq485 y
       have i₂ := eq20363
       grind)
    | exact superpose eq20363 eq485
    | (have j0 := eq485 y
       grind)
    | exact resolve eq485 eq20363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20363
  have eq20397 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq20380
  have eq20411 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq20397
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20397
    | exact resolve eq20397 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20397
  have eq20435 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  have eq20460 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq20411 eq1080
    | exact resolve eq1080 eq20411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080 eq20411
  have eq20590 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq19692 x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19692
    | (have j0 := eq19692 x X0
       grind)
    | exact resolve eq19692 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19692
  have eq21168 : x ≠ (M.op x y) ∨ x = (M.op y y) := by grind
  have eq24484 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq27 eq20460
    | (have j0 := eq20460 (σ x) X0
       grind)
    | exact resolve eq20460 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20460
  have eq76586 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq19969
       have i₂ := eq20590 y
       grind)
    | (have i₁ := eq19969
       have i₂ := eq20590 x
       grind)
    | exact superpose eq20590 eq19969
    | exact resolve eq19969 eq20590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19969 eq20590
  have eq76664 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq76586
       have r₂ := eq21168
       grind)
    | exact resolve eq76586 eq21168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21168 eq76586
  have eq76667 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq76664
    | exact resolve eq76664 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76664
  have eq76699 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq76667 eq20435
    | exact resolve eq20435 eq76667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20435 eq76667
  have eq76723 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq76699
  have eq77298 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq76723 eq24484
    | exact resolve eq24484 eq76723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24484 eq76723
  have eq77417 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq77298
  have eq77434 : x = (M.op y y) := by
    first
    | (have r₁ := eq77417
       have r₂ := eq28
       grind)
    | exact resolve eq77417 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77417
  have eq77688 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq102
       have i₂ := eq77434
       grind)
    | exact superpose eq77434 eq102
    | exact resolve eq102 eq77434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq77693 : (M.op x y) = (k x y) := by grind
  have eq77824 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq77693
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq77693
    | exact resolve eq77693 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77693
  have eq77825 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq77688
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq77688
    | exact resolve eq77688 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77688
  have eq77832 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq77824
       grind)
    | exact superpose eq77824 eq45
    | exact resolve eq45 eq77824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq77862 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq77832
    | exact resolve eq77832 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77832
  have eq84782 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq77825 eq5940
    | (have j0 := eq5940 (σ y)
       grind)
    | exact resolve eq5940 eq77825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5940
  have eq84792 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq77862 eq84782
    | exact resolve eq84782 eq77862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84782
  have eq84810 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq84792
    | exact resolve eq84792 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84792
  have eq84813 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq84810
       have r₂ := eq28
       grind)
    | exact resolve eq84810 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84810
  have eq84928 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq84813
  have eq122300 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq84928 eq77825
    | exact resolve eq77825 eq84928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77825 eq84928
  have eq122324 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq122300
  have eq122365 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq122324
  have eq122555 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq77862 eq122365
    | exact resolve eq122365 eq77862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77862 eq122365
  have eq122585 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq122555
    | exact resolve eq122555 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122555
  have eq122593 : x = y := by
    first
    | (have r₁ := eq122585
       have r₂ := eq28
       grind)
    | exact resolve eq122585 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122585
  have eq122596 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq122593
       grind)
    | exact superpose eq122593 eq19
    | exact resolve eq19 eq122593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq122597 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq122593
       grind)
    | exact superpose eq122593 eq25
    | exact resolve eq25 eq122593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq122791 : x = (M.op x x) := by
    first
    | (have i₁ := eq77434
       have i₂ := eq122593
       grind)
    | exact superpose eq122593 eq77434
    | exact resolve eq77434 eq122593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77434
  have eq122794 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq77824
       have i₂ := eq122593
       grind)
    | exact superpose eq122593 eq77824
    | exact resolve eq77824 eq122593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77824 eq122593
  have eq122951 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq122597
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq122597
    | exact resolve eq122597 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122597
  have eq122972 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq122951 eq27
    | exact resolve eq27 eq122951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq122951
  have eq124809 : x = (M.op x y) := by
    first
    | (have i₁ := eq122791
       have i₂ := eq122596
       grind)
    | exact superpose eq122596 eq122791
    | exact resolve eq122791 eq122596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122596 eq122791
  have eq124810 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq124809 eq21
    | exact resolve eq21 eq124809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq125179 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq124810
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq124810
    | exact resolve eq124810 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124810
  have eq125735 : x = (k x x) := by
    first
    | exact superpose eq124809 eq122794
    | exact resolve eq122794 eq124809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122794 eq124809
  have eq125765 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq485 x
       have i₂ := eq125735
       grind)
    | exact superpose eq125735 eq485
    | (have j0 := eq485 x
       grind)
    | exact resolve eq485 eq125735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485 eq125735
  have eq125788 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq125765
  have eq125802 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq125788
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq125788
    | exact resolve eq125788 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq125788
  have eq125827 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq125179 eq125802
    | exact resolve eq125802 eq125179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125802
  have eq128198 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq125179 eq122972
    | exact resolve eq122972 eq125179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122972 eq125179
  have eq129204 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq125827 eq128198
    | exact resolve eq128198 eq125827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125827 eq128198
  have eq129205 : False := by grind
  exact eq129205

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
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
  have eq42 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq42 (σ X0)
       grind)
    | exact superpose eq42 eq15
    | exact resolve eq15 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq56
    | exact resolve eq56 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq56
  have eq79 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq79 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq79
    | (have j0 := eq79 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq79 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq16
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq225 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq153
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq153
    | (have j1 := eq79 (σ x) (σ y)
       grind)
    | (have r₁ := eq153
       have r₂ := eq79 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq153
       have r₂ := eq79 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq153 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq153
  have eq228 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq225
  have eq229 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq228
       grind)
    | exact superpose eq228 eq16
    | exact resolve eq16 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq230 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq229
       have r₂ := eq65 x
       grind)
    | exact resolve eq229 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq266 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq230
       grind)
    | exact superpose eq230 eq10
    | exact resolve eq10 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq283 : x = y := by
    first
    | (have i₁ := eq266
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq266
    | exact resolve eq266 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq327 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq283
       grind)
    | exact superpose eq283 eq16
    | exact resolve eq16 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq328 : False := by grind
  exact eq328

/-- `Equation1845`: `x = (x ◇ (x ◇ y)) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_y_pxy_pxx_pxy_Equation1845 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1845 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1845.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X2)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
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
  have eq175 : ∀ X0 : G, x = (M.op (M.op x (M.op x y)) (M.op X0 X0)) := by
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
  have eq176 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)) X2
       have i₂ := eq16 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 (M.op X0 X1)) (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq178 (M.op X0 (M.op X0 X1)) (M.op x x) X3
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq178
    | exact resolve eq178 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : ∀ X1 : G, (M.op (M.op x (M.op x y)) x) = (M.op (M.op x (M.op x y)) (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq175 eq178
    | exact resolve eq178 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X1 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq176 eq178
    | exact resolve eq178 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq178 X0 x X3
       have i₂ := eq178 X0 x X1
       grind)
    | (have i₁ := eq178 x x x
       have i₂ := eq178 x X1 x
       grind)
    | exact superpose eq178 eq178
    | exact resolve eq178 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq176 eq554
    | exact resolve eq554 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq554
  have eq590 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq175 eq553
    | exact resolve eq553 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq553
  have eq591 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq552 X0 X1 x
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq552
    | exact resolve eq552 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq614 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq591 X0 x
       have i₂ := eq178 X0 x X1
       grind)
    | (have i₁ := eq591 x x
       have i₂ := eq178 x X1 x
       grind)
    | exact superpose eq178 eq591
    | exact resolve eq591 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq998 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (k X0 X1)) (M.op X2 X2)) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1037 : (M.op x y) = (k x y) ∨ y = (M.op y y) := by
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
  have eq1044 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq1047 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1056 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1037
       grind)
    | exact superpose eq1037 eq41
    | exact resolve eq41 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037
  have eq1057 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1056
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1056
    | exact resolve eq1056 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056
  have eq1059 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1057
    | exact resolve eq1057 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1069 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1059 eq1044
    | exact resolve eq1044 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044 eq1059
  have eq1076 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1069
       have r₂ := eq27
       grind)
    | exact resolve eq1069 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq1081 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1076 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq1076
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq1076
       grind)
    | exact resolve eq13 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq1100 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1081
  have eq1106 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1100 eq153
    | exact resolve eq153 eq1100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq1100
  have eq1109 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq32 eq1106
    | exact resolve eq1106 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1106
  have eq1112 : y = (M.op y y) := by
    first
    | (have j1 := eq1047 y
       grind)
    | (have r₁ := eq1109
       have r₂ := eq1047 y
       grind)
    | exact resolve eq1109 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109
  have eq1116 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1112
       grind)
    | exact superpose eq1112 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq1112
       grind)
    | exact resolve eq13 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1126 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1 y
       have i₂ := eq1112
       grind)
    | exact superpose eq1112 eq178
    | exact resolve eq178 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1127 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq183 y
       have i₂ := eq1112
       grind)
    | exact superpose eq1112 eq183
    | exact resolve eq183 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq1130 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq559 X0 X1 y
       have i₂ := eq1112
       grind)
    | exact superpose eq1112 eq559
    | exact resolve eq559 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq1112
  have eq1135 : y = (k y y) := by grind
  clear eq1116
  have eq1136 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1127
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1127
    | exact resolve eq1127 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127
  have eq1140 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq1135
       grind)
    | exact superpose eq1135 eq41
    | exact resolve eq41 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1135
  have eq1143 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1140
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1140
    | exact resolve eq1140 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1140
  have eq1147 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1136 eq590
    | exact resolve eq590 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq1136
  have eq1162 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1143 eq1047
    | (have j0 := eq1047 (σ y)
       grind)
    | (have r₁ := eq1047 (σ y)
       have r₂ := eq1143
       grind)
    | exact resolve eq1047 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq1163 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1162
  have eq1170 : x = (k (M.op x y) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1147 eq28
    | (have j0 := eq28 x x
       grind)
    | exact resolve eq28 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147
  have eq1212 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1163 eq178
    | exact resolve eq178 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1214 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1163 eq187
    | exact resolve eq187 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq1219 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1163 eq614
    | exact resolve eq614 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614 eq1163
  have eq1224 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq1214
    | exact resolve eq1214 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1231 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1224 eq589
    | exact resolve eq589 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589 eq1224
  have eq1268 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1231 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231
  have eq1439 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op X0 (σ y)) X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | exact superpose eq1219 eq16
    | exact resolve eq16 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1458 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op X0 (σ y)) X0) y) := by
    intro X0
    first
    | (have i₁ := eq1439 X0 x
       have i₂ := eq1130 (M.op (M.op X0 sF3) X0) x
       grind)
    | exact superpose eq1130 eq1439
    | exact resolve eq1439 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439
  have eq1465 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq1219 eq1458
    | exact resolve eq1458 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219 eq1458
  have eq5288 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1170 eq38
    | exact resolve eq38 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1170
  have eq5294 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5288
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5288
    | exact resolve eq5288 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5288
  have eq5313 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq5294 eq998
    | (have j0 := eq998 X0 (σ x) x
       grind)
    | exact resolve eq998 eq5294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq5314 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5313 x
       have i₂ := eq1130 (M.op sF1 sF2) x
       grind)
    | exact superpose eq1130 eq5313
    | exact resolve eq5313 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130 eq5313
  have eq5318 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5314
       have i₂ := eq1465 (M.op sF1 sF2)
       grind)
    | exact superpose eq1465 eq5314
    | exact resolve eq5314 eq1465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465 eq5314
  have eq5320 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq5318
    | (have j1 := eq28 x (σ x)
       grind)
    | exact resolve eq5318 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq5318
  have eq5321 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq5294 eq5320
    | exact resolve eq5320 eq5294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5294 eq5320
  have eq5322 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq5321
    | exact resolve eq5321 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5321
  have eq5323 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq5322
       have r₂ := eq27
       grind)
    | exact resolve eq5322 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5322
  have eq5535 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq5323 eq1212
    | exact resolve eq1212 eq5323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5538 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq5535
    | exact resolve eq5535 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5535
  have eq5568 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5323 eq5538
    | exact resolve eq5538 eq5323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5323 eq5538
  have eq5631 : x ≠ x ∨ x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq5568
       grind)
    | exact superpose eq5568 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq5568
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq5568
       grind)
    | exact resolve eq13 eq5568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5568
  have eq5644 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5631
  have eq5746 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq5644
       grind)
    | exact superpose eq5644 eq40
    | exact resolve eq40 eq5644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq5644
  have eq5753 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5746
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5746
    | exact resolve eq5746 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5746
  have eq6241 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5753 eq1047
    | (have j0 := eq1047 (σ x)
       grind)
    | (have r₁ := eq1047 (σ x)
       have r₂ := eq5753
       grind)
    | exact resolve eq1047 eq5753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5753
  have eq6244 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6241
  have eq6471 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6244 eq1212
    | exact resolve eq1212 eq6244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq6474 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq6471
    | exact resolve eq6471 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq6471
  have eq6505 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6244 eq6474
    | exact resolve eq6474 eq6244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6244 eq6474
  have eq6506 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6505
  have eq6534 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq6506 eq27
    | exact resolve eq27 eq6506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq6545 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq6506 eq1268
    | (have r₁ := eq1268
       have r₂ := eq6506
       grind)
    | exact resolve eq1268 eq6506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268 eq6506
  have eq6555 : (σ x) = (k (σ x) (σ x)) := by grind
  clear eq6545
  have eq6721 : (τ (σ x)) = (k (τ (σ x)) x) := by
    first
    | exact superpose eq6555 eq142
    | exact resolve eq142 eq6555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq6555
  have eq6729 : x = (k x x) := by
    first
    | exact superpose eq30 eq6721
    | exact resolve eq6721 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq6721
  have eq6811 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1047 x
       have i₂ := eq6729
       grind)
    | exact superpose eq6729 eq1047
    | (have j0 := eq1047 x
       grind)
    | (have r₁ := eq1047 x
       have r₂ := eq6729
       grind)
    | exact resolve eq1047 eq6729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047 eq6729
  have eq6814 : x = (M.op x x) := by grind
  clear eq6811
  have eq6863 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1126 x x
       have i₂ := eq6814
       grind)
    | exact superpose eq6814 eq1126
    | exact resolve eq1126 eq6814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq6868 : x = (M.op x y) := by
    first
    | (have i₁ := eq6863
       have i₂ := eq6814
       grind)
    | exact superpose eq6814 eq6863
    | exact resolve eq6863 eq6814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6814 eq6863
  have eq6901 : x = (M.op x y) := by
    first
    | (have i₁ := eq6868
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6868
    | exact resolve eq6868 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq6868
  have eq6950 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq6901
       grind)
    | exact superpose eq6901 eq22
    | exact resolve eq22 eq6901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6901
  have eq7020 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq6950 eq20
    | exact resolve eq20 eq6950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq6950
  have eq7038 : False := by grind
  exact eq7038

/-- `Equation1845`: `x = (x ◇ (x ◇ y)) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_y_y_x_pxy_Equation1845 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1845 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1845.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X2)) = X0 := by
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
  have eq85 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
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
  have eq163 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq85 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq85
    | exact resolve eq85 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq174 : y ≠ (M.op x y) ∨ x = (k y x) := by
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
  have eq176 : ∀ X0 : G, x = (M.op (M.op x (M.op x y)) (M.op X0 X0)) := by
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
  have eq177 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)) X2
       have i₂ := eq16 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 (M.op X0 X1)) (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq179 (M.op X0 (M.op X0 X1)) (M.op x x) X3
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq179
    | exact resolve eq179 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : ∀ X1 : G, (M.op (M.op x (M.op x y)) x) = (M.op (M.op x (M.op x y)) (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq176 eq179
    | exact resolve eq179 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X1 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq177 eq179
    | exact resolve eq179 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq179 X0 x X3
       have i₂ := eq179 X0 x X1
       grind)
    | (have i₁ := eq179 x x x
       have i₂ := eq179 x X1 x
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 X0 X1 x
       have i₂ := eq179 X0 X2 x
       grind)
    | (have i₁ := eq179 X1 X1 X1
       have i₂ := eq179 X1 X1 X2
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X3 X3)) = X0 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X0 x X3
       have i₂ := eq179 X0 x X1
       grind)
    | (have i₁ := eq16 x x x
       have i₂ := eq179 x X1 x
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq578 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X0 (M.op X0 X1)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq179 (M.op X0 (M.op X0 X1)) X2 x
       grind)
    | (have i₁ := eq16 X0 X1 (M.op X0 (M.op X0 X1))
       have i₂ := eq179 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)) X2
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq582 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq184 sF2
       have i₂ := eq179 sF2 sF2 x
       grind)
    | (have i₁ := eq184 x
       have i₂ := eq179 sF2 x x
       grind)
    | exact superpose eq179 eq184
    | exact resolve eq184 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq177 eq548
    | exact resolve eq548 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq584 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq176 eq547
    | exact resolve eq547 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq585 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 X1 x
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq546
    | exact resolve eq546 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq588 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq583 eq13
    | (have j0 := eq13 (σ x) (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq13 (σ x) (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq583
       grind)
    | exact resolve eq13 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) := by grind
  clear eq588
  have eq593 : x ≠ x ∨ (M.op x (M.op x y)) = (k x (M.op x (M.op x y))) := by
    first
    | exact superpose eq584 eq13
    | (have j0 := eq13 x (M.op x (M.op x y))
       grind)
    | (have r₁ := eq13 x (M.op x (M.op x y))
       have r₂ := eq584
       grind)
    | exact resolve eq13 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq594 : (M.op x (M.op x y)) = (k x (M.op x (M.op x y))) := by grind
  clear eq593
  have eq608 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq585 X0 x
       have i₂ := eq179 X0 x X1
       grind)
    | (have i₁ := eq585 x x
       have i₂ := eq179 x X1 x
       grind)
    | exact superpose eq179 eq585
    | exact resolve eq585 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq617 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 (M.op X0 X1))
       have i₂ := eq585 X0 X1
       grind)
    | exact superpose eq585 eq13
    | (have j0 := eq13 X0 (M.op X0 (M.op X0 X1))
       grind)
    | (have r₁ := eq13 X0 (M.op X0 (M.op X0 X1))
       have r₂ := eq585 X0 X1
       grind)
    | exact resolve eq13 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq618 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq617 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq655 : (σ (M.op x (M.op x y))) = (k (σ x) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq594 eq35
    | exact resolve eq35 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq741 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X2 X3)) (M.op (M.op X0 X0) (M.op X1 X1))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 (M.op X0 X0)
       have i₂ := eq553 (M.op X0 X0) X0 X1
       grind)
    | (have i₁ := eq16 X2 X3 (M.op X0 X0)
       have i₂ := eq553 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq553 eq16
    | exact resolve eq16 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op x y)) (M.op (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq176 (M.op X0 X0)
       have i₂ := eq553 (M.op X0 X0) X0 X1
       grind)
    | (have i₁ := eq176 (M.op X0 X0)
       have i₂ := eq553 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq553 eq176
    | exact resolve eq176 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq745 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op x (M.op (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq181 (M.op X0 X0)
       have i₂ := eq553 (M.op X0 X0) X0 X1
       grind)
    | (have i₁ := eq181 (M.op X0 X0)
       have i₂ := eq553 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq553 eq181
    | exact resolve eq181 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq746 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq184 (M.op X0 X0)
       have i₂ := eq553 (M.op X0 X0) X0 X1
       grind)
    | (have i₁ := eq184 (M.op X0 X0)
       have i₂ := eq553 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq553 eq184
    | exact resolve eq184 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq747 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op (M.op X0 X0) (M.op X1 X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq608 X2 (M.op X0 X0)
       have i₂ := eq553 (M.op X0 X0) X0 X1
       grind)
    | (have i₁ := eq608 X2 (M.op X0 X0)
       have i₂ := eq553 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq553 eq608
    | exact resolve eq608 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq898 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq11 X1 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq899 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (k X0 X1)) (M.op X2 X2)) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X1 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq900 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X0 (k X0 X1)) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 X0 X1 X2
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq179
    | (have j1 := eq11 X1 X1
       grind)
    | exact resolve eq179 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq903 : ∀ X0 X1 : G, (M.op (M.op X0 (k X0 X1)) X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq585 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq585
    | (have j1 := eq11 X1 X1
       grind)
    | exact resolve eq585 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq913 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | exact resolve eq12 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq933 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq940 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq945 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq946 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq945 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq957 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq913 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq962 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq957 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq957 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq957 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq957 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq957 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq967 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq946 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq946
    | (have j0 := eq946 (σ X0)
       grind)
    | exact resolve eq946 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1904 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq933
       grind)
    | exact superpose eq933 eq40
    | exact resolve eq40 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1905 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1904
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1904
    | exact resolve eq1904 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1904
  have eq1907 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq1905
    | exact resolve eq1905 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1905
  have eq2528 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq618 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))
       have i₂ := eq16 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq16 eq618
    | exact resolve eq618 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2529 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq618 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))
       have i₂ := eq567 X0 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq567 eq618
    | exact resolve eq618 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq2533 : x = (k (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq176 eq618
    | exact resolve eq618 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2535 : (σ x) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq177 eq618
    | exact resolve eq618 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq2565 : (σ x) = (k (σ (M.op x (M.op x y))) (σ x)) := by
    first
    | exact superpose eq2533 eq39
    | exact resolve eq39 eq2533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq2533
  have eq2566 : (σ x) = (k (σ (M.op x (M.op x y))) (σ x)) := by
    first
    | (have i₁ := eq2565
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2565
    | exact resolve eq2565 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2565
  have eq2568 : (τ (σ x)) = (k (τ (M.op (σ x) (M.op (σ x) (σ y)))) x) := by
    first
    | exact superpose eq2535 eq141
    | exact resolve eq141 eq2535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq2535
  have eq2569 : x = (k (τ (M.op (σ x) (M.op (σ x) (σ y)))) x) := by
    first
    | exact superpose eq29 eq2568
    | exact resolve eq2568 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2568
  have eq2650 : ∀ X0 : G, (τ (σ y)) = (k (τ (M.op (σ y) (M.op (σ y) X0))) y) := by
    intro X0
    first
    | (have i₁ := eq152 (M.op sF3 (M.op sF3 x))
       have i₂ := eq2528 sF3 x
       grind)
    | exact superpose eq2528 eq152
    | exact resolve eq152 eq2528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2528
  have eq2651 : ∀ X0 : G, y = (k (τ (M.op (σ y) (M.op (σ y) X0))) y) := by
    intro X0
    first
    | exact superpose eq31 eq2650
    | exact resolve eq2650 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2650
  have eq2704 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op (M.op x y) (M.op X0 X0))) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq41 (M.op sF0 (M.op x x))
       have i₂ := eq2529 sF0 x
       grind)
    | exact superpose eq2529 eq41
    | exact resolve eq41 eq2529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq2705 : ∀ X0 : G, (τ (σ (M.op x y))) = (k (τ (M.op (σ (M.op x y)) (M.op X0 X0))) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq163 (M.op sF1 (M.op x x))
       have i₂ := eq2529 sF1 x
       grind)
    | exact superpose eq2529 eq163
    | exact resolve eq163 eq2529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq2707 : ∀ X0 : G, (τ (σ y)) = (k (τ (M.op (σ y) (M.op X0 X0))) y) := by
    intro X0
    first
    | (have i₁ := eq152 (M.op sF3 (M.op x x))
       have i₂ := eq2529 sF3 x
       grind)
    | exact superpose eq2529 eq152
    | exact resolve eq152 eq2529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq2529
  have eq2709 : ∀ X0 : G, y = (k (τ (M.op (σ y) (M.op X0 X0))) y) := by
    intro X0
    first
    | exact superpose eq31 eq2707
    | exact resolve eq2707 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2707
  have eq2711 : ∀ X0 : G, (M.op x y) = (k (τ (M.op (σ (M.op x y)) (M.op X0 X0))) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq28 eq2705
    | exact resolve eq2705 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2705
  have eq2712 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op (M.op x y) (M.op X0 X0))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq2704
    | (have j0 := eq2704 X0
       grind)
    | exact resolve eq2704 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2704
  have eq20938 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1907 eq940
    | exact resolve eq940 eq1907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20947 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq20938
       have r₂ := eq27
       grind)
    | exact resolve eq20938 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20938
  have eq20990 : y = (k (τ (M.op (σ y) (σ y))) y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20947 eq2709
    | exact resolve eq2709 eq20947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21049 : y = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20947 eq20990
    | exact resolve eq20990 eq20947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20947 eq20990
  have eq21066 : y = (k y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq31 eq21049
    | exact resolve eq21049 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21049
  have eq21070 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (k y y) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq21066
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq21066
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq21066
       have r₂ := eq13 x y
       grind)
    | exact resolve eq21066 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21066
  have eq21073 : y = (k (τ (M.op (σ y) (σ x))) y) ∨ y = (k y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21070 eq2651
    | exact resolve eq2651 eq21070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2651
  have eq21082 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ y = (k y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21070 eq585
    | exact resolve eq585 eq21070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21096 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21070 eq21082
    | exact resolve eq21082 eq21070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21082
  have eq21104 : y = (k (τ (σ x)) y) ∨ y = (k y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21070 eq21073
    | exact resolve eq21073 eq21070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21070 eq21073
  have eq21107 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq21096
    | exact resolve eq21096 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21096
  have eq21111 : y = (k x y) ∨ y = (k y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq21104
    | exact resolve eq21104 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21104
  have eq21115 : y = (k y y) ∨ y = (k x y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq21111
       have r₂ := eq13 x y
       grind)
    | exact resolve eq21111 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21111
  have eq21122 : y ≠ y ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq946 y
       have i₂ := eq21115
       grind)
    | exact superpose eq21115 eq946
    | (have j0 := eq946 y
       grind)
    | (have r₁ := eq946 y
       have r₂ := eq21115
       grind)
    | exact resolve eq946 eq21115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21130 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq967 y
       have i₂ := eq21115
       grind)
    | exact superpose eq21115 eq967
    | (have j0 := eq967 y
       grind)
    | exact resolve eq967 eq21115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21115
  have eq21134 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by grind
  clear eq21130
  have eq21136 : y = (k x y) ∨ y = (M.op y y) := by grind
  clear eq21122
  have eq21137 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq21134
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21134
    | exact resolve eq21134 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21134
  have eq21147 : y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq933
       have i₂ := eq21136
       grind)
    | exact superpose eq21136 eq933
    | exact resolve eq933 eq21136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933
  have eq21148 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq21136
       grind)
    | exact superpose eq21136 eq35
    | exact resolve eq35 eq21136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21150 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 X0)) ∨ y = (M.op y y) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq899 x y X0
       have i₂ := eq21136
       grind)
    | exact superpose eq21136 eq899
    | (have j0 := eq899 y y x
       grind)
    | exact resolve eq899 eq21136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq21151 : y ≠ y ∨ x = (k y x) ∨ y = (M.op y y) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq898 x y
       have i₂ := eq21136
       grind)
    | exact superpose eq21136 eq898
    | (have j0 := eq898 x y
       grind)
    | (have r₁ := eq898 x y
       have r₂ := eq21136
       grind)
    | exact resolve eq898 eq21136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898 eq21136
  have eq21152 : y ≠ y ∨ x = (k y x) ∨ y = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq21151
  have eq21153 : y = (M.op y y) ∨ x = (k y x) ∨ x = (M.op y x) := by grind
  clear eq21152
  have eq21154 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 X0)) ∨ y = (M.op y y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq21150 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21150
  have eq21155 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq21147
  have eq21157 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 X0)) ∨ y = (M.op y y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq21154 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21154
    | (have j0 := eq21154 X0
       grind)
    | exact resolve eq21154 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21154
  have eq21159 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq21148
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21148
    | exact resolve eq21148 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21148
  have eq21165 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = X0 ∨ (k X0 (σ y)) = X0 ∨ y = (k x y) := by
    intro X0
    first
    | exact superpose eq21137 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq21137
       grind)
    | exact resolve eq12 eq21137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21137
  have eq21243 : ∀ X0 : G, y = (k x y) ∨ (k X0 (σ y)) = X0 ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq21165 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21165
  have eq21296 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) ∨ x = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq21159 eq1907
    | exact resolve eq1907 eq21159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1907 eq21159
  have eq21306 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq21296
  have eq22087 : y ≠ y ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq946 y
       have i₂ := eq21107
       grind)
    | exact superpose eq21107 eq946
    | (have j0 := eq946 y
       grind)
    | (have r₁ := eq946 y
       have r₂ := eq21107
       grind)
    | exact resolve eq946 eq21107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22094 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = X0 ∨ (k X0 y) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq962 y X0
       have i₂ := eq21107
       grind)
    | exact superpose eq21107 eq962
    | (have j0 := eq962 y X0
       grind)
    | (have r₁ := eq962 y x
       have r₂ := eq21107
       grind)
    | exact resolve eq962 eq21107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962 eq21107
  have eq22100 : ∀ X0 : G, x = (M.op y x) ∨ (k X0 y) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq22094 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22094
  have eq22101 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq22087
  have eq22124 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq181 y
       have i₂ := eq22101
       grind)
    | exact superpose eq22101 eq181
    | exact resolve eq181 eq22101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22133 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq553 X0 X1 y
       have i₂ := eq22101
       grind)
    | exact superpose eq22101 eq553
    | exact resolve eq553 eq22101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22188 : ∀ X0 : G, (M.op y y) = (M.op y (M.op X0 X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq179 y y X0
       have i₂ := eq22101
       grind)
    | exact superpose eq22101 eq179
    | exact resolve eq179 eq22101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22210 : ∀ X0 : G, y = (M.op y (M.op X0 X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq22101 eq22188
    | exact resolve eq22188 eq22101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22101 eq22188
  have eq22218 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq22124
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22124
    | exact resolve eq22124 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22124
  have eq22404 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq181 y
       have i₂ := eq21155
       grind)
    | exact superpose eq21155 eq181
    | exact resolve eq181 eq21155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22465 : y ≠ y ∨ y = (k y y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq21155
       grind)
    | exact superpose eq21155 eq13
    | (have j0 := eq13 y y
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq21155
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq21155
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq21155
       grind)
    | exact resolve eq13 eq21155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21155
  have eq22479 : y = (k y y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq22465
  have eq22499 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq22404
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22404
    | exact resolve eq22404 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22404
  have eq22876 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op (M.op X0 X0) (M.op X1 X1))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq22218 eq742
    | exact resolve eq742 eq22218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq22906 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op X0 X0) y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq22133 eq22876
    | exact resolve eq22876 eq22133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22876
  have eq23030 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq181 y
       have i₂ := eq21306
       grind)
    | exact superpose eq21306 eq181
    | exact resolve eq181 eq21306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21306
  have eq23124 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq23030
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23030
    | exact resolve eq23030 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23030
  have eq23431 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq967 y
       have i₂ := eq22479
       grind)
    | exact superpose eq22479 eq967
    | (have j0 := eq967 y
       grind)
    | exact resolve eq967 eq22479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22479
  have eq23435 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq23431
  have eq23438 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq23435
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23435
    | exact resolve eq23435 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23435
  have eq25157 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq23438 eq184
    | exact resolve eq184 eq23438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25223 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ y) (σ y)) X0)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq23438 eq578
    | exact resolve eq578 eq23438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25241 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq23438 eq25223
    | exact resolve eq25223 eq23438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23438 eq25223
  have eq25265 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq25157
    | exact resolve eq25157 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25157
  have eq25750 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq25265 eq583
    | exact resolve eq583 eq25265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25265
  have eq32063 : ∀ X0 : G, (σ y) = (k (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq35 y
       have i₂ := eq21243 X0
       grind)
    | exact superpose eq21243 eq35
    | (have j1 := eq21243 X0
       grind)
    | exact resolve eq35 eq21243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq21243
  have eq32072 : ∀ X0 : G, (σ y) = (k (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq32063 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32063
    | (have j0 := eq32063 X0
       grind)
    | exact resolve eq32063 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32063
  have eq32635 : ∀ X0 X1 : G, y = (M.op y (M.op (M.op X0 X0) (M.op X1 X1))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq22210 (M.op X0 X0)
       have i₂ := eq553 (M.op X0 X0) X0 X1
       grind)
    | (have i₁ := eq22210 (M.op X0 X0)
       have i₂ := eq553 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq553 eq22210
    | exact resolve eq22210 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553 eq22210
  have eq32737 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 X0) y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq22133 eq32635
    | exact resolve eq32635 eq22133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22133 eq32635
  have eq41290 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have j0 := eq32072 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32072
  have eq87500 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21157 eq747
    | exact resolve eq747 eq21157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747 eq21157
  have eq87558 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq22499 eq87500
    | exact resolve eq87500 eq22499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22499 eq87500
  have eq87625 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq87558 eq177
    | exact resolve eq177 eq87558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87627 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op x y)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq87558 eq179
    | exact resolve eq179 eq87558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87631 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq87558 eq184
    | exact resolve eq184 eq87558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87752 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq87558 eq13
    | (have j0 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq87558
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq87558
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq87558
       grind)
    | exact resolve eq13 eq87558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87558
  have eq87784 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by grind
  clear eq87752
  have eq87882 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq22218 eq87631
    | exact resolve eq87631 eq22218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87631
  have eq87884 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op x y)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq22218 eq87625
    | exact resolve eq87625 eq22218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87625
  have eq87929 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq87882
    | exact resolve eq87882 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87882
  have eq87930 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op x y)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq87884
    | exact resolve eq87884 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87884
  have eq87956 : (σ y) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq22218 eq87929
    | exact resolve eq87929 eq22218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87929
  have eq87957 : (σ x) = (M.op (σ y) (M.op x y)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq22218 eq87930
    | exact resolve eq87930 eq22218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87930
  have eq89150 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq87784 eq967
    | (have j0 := eq967 (M.op x y)
       grind)
    | exact resolve eq967 eq87784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87784
  have eq89179 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by grind
  clear eq89150
  have eq89185 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq89179
    | exact resolve eq89179 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89179
  have eq89193 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq23124 eq89185
    | exact resolve eq89185 eq23124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23124 eq89185
  have eq89399 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq87956 eq578
    | exact resolve eq578 eq87956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87956
  have eq89433 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq89399
    | (have j0 := eq89399 X0
       grind)
    | exact resolve eq89399 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89399
  have eq89455 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ y) X0)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq22218 eq89433
    | exact resolve eq89433 eq22218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89433
  have eq91605 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq89193 eq561
    | exact resolve eq561 eq89193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq91607 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ y) (σ y)) X0)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq89193 eq578
    | exact resolve eq578 eq89193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91682 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq89193 eq91607
    | exact resolve eq91607 eq89193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89193 eq91607
  have eq91684 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op x y)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq87627 eq91605
    | exact resolve eq91605 eq87627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87627 eq91605
  have eq91759 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq89455 eq91682
    | exact resolve eq91682 eq89455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89455 eq91682
  have eq91760 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq87957 eq91684
    | exact resolve eq91684 eq87957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87957 eq91684
  have eq91794 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq91759 eq91760
    | exact resolve eq91760 eq91759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91759 eq91760
  have eq96219 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ x)) X0)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq91794 eq578
    | exact resolve eq578 eq91794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96274 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq91794 eq96219
    | exact resolve eq96219 eq91794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91794 eq96219
  have eq96334 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq582 eq96274
    | (have j0 := eq96274 (σ y)
       grind)
    | exact resolve eq96274 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96274
  have eq96374 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq22218 eq96334
    | exact resolve eq96334 eq22218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22218 eq96334
  have eq96411 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq96374
    | exact resolve eq96374 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96374
  have eq96461 : x = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq96411 eq584
    | exact resolve eq584 eq96411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96411
  have eq220347 : ∀ X0 : G, y = (M.op (M.op y x) y) ∨ (k X0 y) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq585 y x
       have i₂ := eq22100 X0
       grind)
    | exact superpose eq22100 eq585
    | (have j1 := eq22100 X0
       grind)
    | exact resolve eq585 eq22100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220394 : ∀ X0 : G, y = (M.op x y) ∨ (k X0 y) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq22100 eq220347
    | (have j0 := eq220347 X0
       have j1 := eq22100 X0
       grind)
    | exact resolve eq220347 eq22100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22100 eq220347
  have eq220414 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq220394 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq220394
    | (have j0 := eq220394 X0
       grind)
    | exact resolve eq220394 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220394
  have eq220799 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq946 y
       have i₂ := eq220414 y
       grind)
    | exact superpose eq220414 eq946
    | (have j0 := eq946 y
       have j1 := eq220414 y
       grind)
    | (have r₁ := eq946 y
       have r₂ := eq220414 y
       grind)
    | exact resolve eq946 eq220414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220414
  have eq221064 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq220799
  have eq221065 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq221064
  have eq221410 : x = (M.op (M.op x (M.op x y)) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq176 y
       have i₂ := eq221065
       grind)
    | exact superpose eq221065 eq176
    | exact resolve eq176 eq221065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221415 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq181 y
       have i₂ := eq221065
       grind)
    | exact superpose eq221065 eq181
    | exact resolve eq181 eq221065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq221418 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq184 y
       have i₂ := eq221065
       grind)
    | exact superpose eq221065 eq184
    | exact resolve eq184 eq221065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221472 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2712 y
       have i₂ := eq221065
       grind)
    | exact superpose eq221065 eq2712
    | exact resolve eq2712 eq221065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2712
  have eq221649 : y ≠ y ∨ y = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq221065
       grind)
    | exact superpose eq221065 eq13
    | (have j0 := eq13 y y
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq221065
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq221065
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq221065
       grind)
    | exact resolve eq13 eq221065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221065
  have eq221694 : y = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq221649
  have eq221853 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq221415
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq221415
    | exact resolve eq221415 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221415
  have eq221899 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq967 y
       have i₂ := eq221694
       grind)
    | exact superpose eq221694 eq967
    | (have j0 := eq967 y
       grind)
    | exact resolve eq967 eq221694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967 eq221694
  have eq221935 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq221899
  have eq221941 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq221935
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq221935
    | exact resolve eq221935 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221935
  have eq221950 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq221853 eq176
    | exact resolve eq176 eq221853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq221954 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq221853 eq584
    | exact resolve eq584 eq221853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq222191 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq221941 eq179
    | exact resolve eq179 eq221941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222196 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq221941 eq184
    | exact resolve eq184 eq221941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221941
  have eq222621 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq222196
    | exact resolve eq222196 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222196
  have eq223611 : x = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq221853 eq221410
    | exact resolve eq221410 eq221853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221410
  have eq223715 : x = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq223611
  have eq224394 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq221418 eq222621
    | exact resolve eq222621 eq221418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222621
  have eq224441 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq224394
  have eq233888 : ∀ X0 : G, (M.op (σ (M.op (M.op x y) y)) (σ (M.op x y))) = (M.op (σ (M.op (M.op x y) y)) (M.op X0 X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op x y)) (σ (M.op (M.op x y) y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq221472 eq900
    | (have j0 := eq900 (σ (M.op x y)) (σ (M.op x y)) x
       grind)
    | exact resolve eq900 eq221472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq233916 : ∀ X0 : G, (k (σ (M.op (M.op x y) y)) (σ (M.op x y))) = (M.op (σ (M.op (M.op x y) y)) (M.op X0 X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op x y)) (σ (M.op (M.op x y) y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq11 eq233888
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq233888 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233888
  have eq233949 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) y)) (M.op X0 X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op x y)) (σ (M.op (M.op x y) y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq221472 eq233916
    | exact resolve eq233916 eq221472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221472 eq233916
  have eq233965 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op x y)) (σ (M.op (M.op x y) y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq223715 eq233949
    | exact resolve eq233949 eq223715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233949
  have eq233974 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op x y)) (σ (M.op (M.op x y) y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq233965 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq233965
    | (have j0 := eq233965 X0
       grind)
    | exact resolve eq233965 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233965
  have eq233983 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op x y)) (σ (M.op (M.op x y) y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq184 eq233974
    | exact resolve eq233974 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233974
  have eq233992 : (σ (M.op x y)) = (M.op (σ x) y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op x y)) (σ (M.op (M.op x y) y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq221418 eq233983
    | exact resolve eq233983 eq221418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233983
  have eq234000 : (σ (M.op x y)) = (M.op (σ x) y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq223715 eq233992
    | exact resolve eq233992 eq223715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223715 eq233992
  have eq234007 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq234000
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq234000
    | exact resolve eq234000 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234000
  have eq234012 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq224441 eq234007
    | exact resolve eq234007 eq224441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234007
  have eq234015 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq234012
       have r₂ := eq27
       grind)
    | exact resolve eq234012 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234012
  have eq261954 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (M.op X0 X0) (M.op X1 X1))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq234015 eq741
    | exact resolve eq741 eq234015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq262019 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (M.op X0 X0) (M.op X1 X1))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq234015 eq261954
    | exact resolve eq261954 eq234015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234015 eq261954
  have eq262047 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq746 eq262019
    | exact resolve eq262019 eq746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746 eq262019
  have eq262058 : (σ (M.op x y)) = (M.op (σ x) y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq221418 eq262047
    | exact resolve eq262047 eq221418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221418 eq262047
  have eq262064 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq224441 eq262058
    | exact resolve eq262058 eq224441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224441 eq262058
  have eq262068 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq262064
       have r₂ := eq27
       grind)
    | exact resolve eq262064 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262064
  have eq262141 : (M.op x y) = (k (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq262068 eq2711
    | exact resolve eq2711 eq262068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2711
  have eq262382 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq262068 eq222191
    | exact resolve eq222191 eq262068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222191
  have eq262383 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq262382
  have eq262469 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq262068 eq262383
    | exact resolve eq262383 eq262068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262383
  have eq262584 : (M.op x y) = (k (τ (σ (M.op x y))) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq262068 eq262141
    | exact resolve eq262141 eq262068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262068 eq262141
  have eq262669 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq262584
    | exact resolve eq262584 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq262584
  have eq263364 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq262669 eq946
    | (have j0 := eq946 (M.op x y)
       grind)
    | (have r₁ := eq946 (M.op x y)
       have r₂ := eq262669
       grind)
    | exact resolve eq946 eq262669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262669
  have eq263409 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq263364
  have eq264175 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op (M.op X0 X0) (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq263409 eq745
    | exact resolve eq745 eq263409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq264389 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq263409 eq221950
    | exact resolve eq221950 eq263409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221950
  have eq264472 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq264389
  have eq264576 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq263409 eq264472
    | exact resolve eq264472 eq263409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263409 eq264472
  have eq264683 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op X0 X0) (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq221853 eq264175
    | exact resolve eq264175 eq221853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221853 eq264175
  have eq264785 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op (M.op X0 X0) (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq264576 eq264683
    | exact resolve eq264683 eq264576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264683
  have eq264862 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq264576 eq177
    | exact resolve eq177 eq264576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq264866 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq264576 eq583
    | exact resolve eq583 eq264576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq264867 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq264576 eq589
    | exact resolve eq589 eq264576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq264878 : x = (k (τ (M.op (σ x) (σ y))) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq264576 eq2569
    | exact resolve eq2569 eq264576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264908 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq264576 eq25750
    | exact resolve eq25750 eq264576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25750
  have eq264975 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq264908
  have eq265014 : x = (k (τ (M.op (σ x) (σ y))) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq264878
    | exact resolve eq264878 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264878
  have eq265025 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq264867
    | exact resolve eq264867 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264867
  have eq265026 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq264866
    | exact resolve eq264866 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264866
  have eq265030 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq264862
    | (have j0 := eq264862 X0
       grind)
    | exact resolve eq264862 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264862
  have eq265041 : x = (k (τ (σ y)) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq264576 eq265014
    | exact resolve eq265014 eq264576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265014
  have eq265053 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq264576 eq265025
    | exact resolve eq265025 eq264576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265025
  have eq265054 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq264576 eq265026
    | exact resolve eq265026 eq264576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265026
  have eq265058 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 X0)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq264576 eq265030
    | exact resolve eq265030 eq264576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265030
  have eq265061 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq265041
    | exact resolve eq265041 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265041
  have eq265066 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq265061
       have r₂ := eq174
       grind)
    | exact resolve eq265061 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265061
  have eq265074 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq265066
       grind)
    | exact superpose eq265066 eq36
    | exact resolve eq36 eq265066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq265066
  have eq265100 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq265074
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq265074
    | exact resolve eq265074 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265074
  have eq266865 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq265054 eq25241
    | exact resolve eq25241 eq265054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25241
  have eq266936 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq266865
  have eq266970 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq264975 eq266936
    | exact resolve eq266936 eq264975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264975 eq266936
  have eq290363 : y = (M.op (M.op y x) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq585 y x
       have i₂ := eq266970
       grind)
    | exact superpose eq266970 eq585
    | exact resolve eq585 eq266970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290420 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq266970 eq290363
    | exact resolve eq290363 eq266970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266970 eq290363
  have eq290442 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq290420
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq290420
    | exact resolve eq290420 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290420
  have eq290443 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq290442
  have eq290455 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq290443 eq31
    | exact resolve eq31 eq290443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291098 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 X0)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq290443 eq265058
    | exact resolve eq265058 eq290443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265058
  have eq291099 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq290443 eq265100
    | exact resolve eq265100 eq290443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265100 eq290443
  have eq291124 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq291099
  have eq291125 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 X0)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq291098 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291098
  have eq291312 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq184 eq291125
    | exact resolve eq291125 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq291125
  have eq291534 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq290455
    | exact resolve eq290455 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq290455
  have eq291536 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq264576 eq291312
    | exact resolve eq291312 eq264576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264576 eq291312
  have eq291616 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq291536
    | exact resolve eq291536 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291536
  have eq291651 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq291534
       grind)
    | exact superpose eq291534 eq18
    | exact resolve eq18 eq291534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291652 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq291534
       grind)
    | exact superpose eq291534 eq24
    | exact resolve eq24 eq291534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291735 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op X0 X0) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22906 X0
       have i₂ := eq291534
       grind)
    | exact superpose eq291534 eq22906
    | exact resolve eq22906 eq291534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22906
  have eq291798 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op (M.op X0 X0) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq32737 X0
       have i₂ := eq291534
       grind)
    | exact superpose eq291534 eq32737
    | exact resolve eq32737 eq291534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32737 eq291534
  have eq291941 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op (M.op X0 X0) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq264785 eq291798
    | (have j0 := eq291798 X0
       have j1 := eq264785 X0
       grind)
    | exact resolve eq291798 eq264785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264785 eq291798
  have eq291942 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op (M.op X0 X0) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq291941 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291941
  have eq291982 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op X0 X0) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq221954 eq291735
    | (have j0 := eq291735 X0
       grind)
    | exact resolve eq291735 eq221954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221954 eq291735
  have eq291983 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op X0 X0) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq291982 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291982
  have eq292058 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq291652
    | exact resolve eq291652 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291652
  have eq292068 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq291942 eq291983
    | exact resolve eq291983 eq291942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291942 eq291983
  have eq292069 : x = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq292068
  have eq293603 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq291651 eq655
    | exact resolve eq655 eq291651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655 eq291651
  have eq293723 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq293603
    | exact resolve eq293603 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293603
  have eq293737 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq292058 eq293723
    | exact resolve eq293723 eq292058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293723
  have eq293743 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq265053 eq293737
    | exact resolve eq293737 eq265053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265053 eq293737
  have eq293744 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq293743
  have eq293753 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq293744 eq940
    | exact resolve eq940 eq293744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq293979 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x y) (M.op X0 X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq292069 eq179
    | exact resolve eq179 eq292069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq294049 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq292069 eq293979
    | exact resolve eq293979 eq292069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292069 eq293979
  have eq324078 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq293744 eq903
    | (have j0 := eq903 (σ y) (σ y)
       grind)
    | exact resolve eq903 eq293744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293744
  have eq324656 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq324078
    | exact resolve eq324078 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324078
  have eq324931 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq293753 eq324656
    | exact resolve eq324656 eq293753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293753 eq324656
  have eq324932 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq324931
  have eq325634 : y = (k (τ (M.op (σ y) (σ y))) y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq324932 eq2709
    | exact resolve eq2709 eq324932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2709
  have eq325945 : (M.op x y) = (k (τ (M.op (σ y) (σ y))) (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq265054 eq325634
    | exact resolve eq325634 eq265054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325634
  have eq325964 : (M.op x y) = (k (τ (σ y)) (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq324932 eq325945
    | exact resolve eq325945 eq324932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324932 eq325945
  have eq325974 : (M.op x y) = (k y (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq325964
    | exact resolve eq325964 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325964
  have eq325977 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq265054 eq325974
    | exact resolve eq325974 eq265054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265054 eq325974
  have eq326558 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq325977 eq585
    | exact resolve eq585 eq325977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq326624 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq325977 eq326558
    | exact resolve eq326558 eq325977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325977 eq326558
  have eq326659 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq326624
    | exact resolve eq326624 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326624
  have eq326679 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq326659 eq946
    | (have j0 := eq946 (M.op x y)
       grind)
    | (have r₁ := eq946 (M.op x y)
       have r₂ := eq326659
       grind)
    | exact resolve eq946 eq326659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326659
  have eq326728 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq326679
  have eq327079 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq326728 eq294049
    | exact resolve eq294049 eq326728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294049
  have eq327134 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq327079
  have eq327234 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq326728 eq327134
    | exact resolve eq327134 eq326728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326728 eq327134
  have eq327235 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq327234
  have eq327339 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq327235 eq27
    | exact resolve eq27 eq327235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327235
  have eq327525 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq292058 eq327339
    | (have r₁ := eq327339
       have r₂ := eq292058
       grind)
    | exact resolve eq327339 eq292058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292058 eq327339
  have eq327526 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq327525
  have eq327527 : x = (M.op x y) ∨ x = y := by grind
  clear eq327526
  have eq327528 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq327527
       grind)
    | exact superpose eq327527 eq18
    | exact resolve eq18 eq327527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327529 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq327527
       grind)
    | exact superpose eq327527 eq22
    | exact resolve eq22 eq327527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327570 : (σ x) = (k (σ (M.op (M.op x y) (M.op x y))) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq2566
       have i₂ := eq327527
       grind)
    | exact superpose eq327527 eq2566
    | exact resolve eq2566 eq327527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2566
  have eq327732 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq96461
       have i₂ := eq327527
       grind)
    | exact superpose eq327527 eq96461
    | exact resolve eq96461 eq327527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96461
  have eq327851 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq327529
    | exact resolve eq327529 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327529
  have eq328055 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq327851 eq262469
    | exact resolve eq262469 eq327851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262469
  have eq328210 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq328055
    | exact resolve eq328055 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328055
  have eq328409 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq291616 eq328210
    | exact resolve eq328210 eq291616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328210
  have eq328410 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq328409
  have eq328967 : x = (k (τ (M.op (σ x) (σ y))) x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq328410 eq2569
    | exact resolve eq2569 eq328410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2569
  have eq329148 : x = (k (τ (M.op (σ x) (σ y))) x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq328967
    | exact resolve eq328967 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328967
  have eq329206 : x = (k (τ (σ y)) x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq328410 eq329148
    | exact resolve eq329148 eq328410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329148
  have eq329239 : x = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq329206
    | exact resolve eq329206 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq329206
  have eq329256 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq329239
       have r₂ := eq174
       grind)
    | exact resolve eq329239 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq329239
  have eq329273 : (M.op x y) = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq329256
       have i₂ := eq327527
       grind)
    | exact superpose eq327527 eq329256
    | exact resolve eq329256 eq327527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329256
  have eq338657 : y = (M.op (M.op y (M.op x y)) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq329273 eq903
    | (have j0 := eq903 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq903 eq329273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903 eq329273
  have eq338680 : y = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq327732 eq338657
    | exact resolve eq338657 eq327732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327732 eq338657
  have eq338681 : y = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq338680
  have eq338695 : y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq327528 eq338681
    | exact resolve eq338681 eq327528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327528 eq338681
  have eq338709 : y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq291616 eq338695
    | exact resolve eq338695 eq291616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291616 eq338695
  have eq338710 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq338709
  have eq338815 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq338710 eq327570
    | exact resolve eq327570 eq338710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327570 eq338710
  have eq339423 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq338815
    | exact resolve eq338815 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338815
  have eq339550 : (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq327851 eq339423
    | exact resolve eq339423 eq327851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339423
  have eq339625 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq291124 eq339550
    | exact resolve eq339550 eq291124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291124 eq339550
  have eq339626 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq339625
  have eq342776 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq339626 eq946
    | (have j0 := eq946 (σ x)
       grind)
    | (have r₁ := eq946 (σ x)
       have r₂ := eq339626
       grind)
    | exact resolve eq946 eq339626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339626
  have eq342826 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq342776
  have eq345403 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ x)) X0)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq342826 eq578
    | exact resolve eq578 eq342826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq345532 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq342826 eq345403
    | exact resolve eq345403 eq342826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342826 eq345403
  have eq345704 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq582 eq345532
    | (have j0 := eq345532 (σ y)
       grind)
    | exact resolve eq345532 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq345532
  have eq345832 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq328410 eq345704
    | exact resolve eq345704 eq328410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328410 eq345704
  have eq345914 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq345832
    | exact resolve eq345832 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345832
  have eq345915 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq345914
  have eq345963 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq345915 eq27
    | exact resolve eq27 eq345915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345915
  have eq346350 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq327851 eq345963
    | (have r₁ := eq345963
       have r₂ := eq327851
       grind)
    | exact resolve eq345963 eq327851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327851 eq345963
  have eq346352 : y = (M.op x y) ∨ x = y := by grind
  clear eq346350
  have eq346601 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq346352
  have eq346604 : x = y := by
    first
    | (have r₁ := eq346601
       have r₂ := eq327527
       grind)
    | exact resolve eq346601 eq327527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327527 eq346601
  have eq346850 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq346604
       grind)
    | exact superpose eq346604 eq18
    | exact resolve eq18 eq346604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq346851 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq346604
       grind)
    | exact superpose eq346604 eq24
    | exact resolve eq24 eq346604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq346891 : x = (M.op x x) ∨ x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq21153
       have i₂ := eq346604
       grind)
    | exact superpose eq346604 eq21153
    | exact resolve eq21153 eq346604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21153 eq346604
  have eq347262 : x = (M.op x x) ∨ x = (k x x) := by grind
  clear eq346891
  have eq347471 : x = (M.op x x) := by
    first
    | (have j1 := eq946 x
       grind)
    | (have r₁ := eq347262
       have r₂ := eq946 x
       grind)
    | exact resolve eq347262 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946 eq347262
  have eq347498 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq346851
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq346851
    | exact resolve eq346851 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346851
  have eq347551 : x = (M.op x y) := by
    first
    | (have i₁ := eq347471
       have i₂ := eq346850
       grind)
    | exact superpose eq346850 eq347471
    | exact resolve eq347471 eq346850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346850 eq347471
  have eq347567 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq347498 eq26
    | exact resolve eq26 eq347498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq347917 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq347498 eq41290
    | (have r₁ := eq41290
       have r₂ := eq347498
       grind)
    | exact resolve eq41290 eq347498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41290 eq347498
  have eq348262 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq347917
  have eq348439 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq348262
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq348262 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348262
  have eq349549 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq347551
       grind)
    | exact superpose eq347551 eq22
    | exact resolve eq22 eq347551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq347551
  have eq350241 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq349549 eq20
    | exact resolve eq20 eq349549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq349549
  have eq353679 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq347567 eq11
    | exact resolve eq11 eq347567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347567
  have eq353720 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq353679
  have eq353732 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq348439 eq353720
    | exact resolve eq353720 eq348439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348439 eq353720
  have eq353733 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq353732
  have eq354317 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq353733 eq27
    | exact resolve eq27 eq353733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq353733
  have eq354531 : False := by grind
  exact eq354531

/-- `Equation1845`: `x = (x ◇ (x ◇ y)) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pxy_pxx_pxy_Equation1845 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1845 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1845.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X2)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
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
  have eq175 : ∀ X0 : G, x = (M.op (M.op x (M.op x y)) (M.op X0 X0)) := by
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
  have eq176 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)) X2
       have i₂ := eq16 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 (M.op X0 X1)) (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq178 (M.op X0 (M.op X0 X1)) (M.op x x) X3
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq178
    | exact resolve eq178 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X1 : G, (M.op (M.op x (M.op x y)) x) = (M.op (M.op x (M.op x y)) (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq175 eq178
    | exact resolve eq178 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : ∀ X1 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq176 eq178
    | exact resolve eq178 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq178 X0 x X3
       have i₂ := eq178 X0 x X1
       grind)
    | (have i₁ := eq178 x x x
       have i₂ := eq178 x X1 x
       grind)
    | exact superpose eq178 eq178
    | exact resolve eq178 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq576 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq176 eq543
    | exact resolve eq543 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq543
  have eq577 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq175 eq542
    | exact resolve eq542 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq542
  have eq578 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq541 X0 X1 x
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq541
    | exact resolve eq541 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq597 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq578 X0 x
       have i₂ := eq178 X0 x X1
       grind)
    | (have i₁ := eq578 x x
       have i₂ := eq178 x X1 x
       grind)
    | exact superpose eq178 eq578
    | exact resolve eq578 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq1033 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (k X0 X1)) (M.op X2 X2)) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1072 : (M.op x y) = (k x y) ∨ y = (M.op y y) := by
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
  have eq1079 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq1083 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1090 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1072
       grind)
    | exact superpose eq1072 eq41
    | exact resolve eq41 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1091 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1090
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1090
    | exact resolve eq1090 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1093 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1091
    | exact resolve eq1091 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq1103 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1093 eq1079
    | exact resolve eq1079 eq1093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079 eq1093
  have eq1110 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1103
       have r₂ := eq27
       grind)
    | exact resolve eq1103 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1126 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1110 eq179
    | exact resolve eq179 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1137 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1110 eq1126
    | exact resolve eq1126 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110 eq1126
  have eq1152 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1137 eq153
    | exact resolve eq153 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq1137
  have eq1155 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq32 eq1152
    | exact resolve eq1152 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1152
  have eq1158 : y = (M.op y y) := by
    first
    | (have j1 := eq1083 y
       grind)
    | (have r₁ := eq1155
       have r₂ := eq1083 y
       grind)
    | exact resolve eq1155 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155
  have eq1172 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1 y
       have i₂ := eq1158
       grind)
    | exact superpose eq1158 eq178
    | exact resolve eq178 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1173 : (k y y) = (M.op y y) := by
    first
    | (have i₁ := eq179 y
       have i₂ := eq1158
       grind)
    | exact superpose eq1158 eq179
    | exact resolve eq179 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1174 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq180 y
       have i₂ := eq1158
       grind)
    | exact superpose eq1158 eq180
    | exact resolve eq180 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1177 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq548 X0 X1 y
       have i₂ := eq1158
       grind)
    | exact superpose eq1158 eq548
    | exact resolve eq548 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq1182 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1174
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1174
    | exact resolve eq1174 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174
  have eq1183 : y = (k y y) := by
    first
    | (have i₁ := eq1173
       have i₂ := eq1158
       grind)
    | exact superpose eq1158 eq1173
    | exact resolve eq1173 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158 eq1173
  have eq1188 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1182 eq577
    | exact resolve eq577 eq1182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577 eq1182
  have eq1200 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq1183
       grind)
    | exact superpose eq1183 eq41
    | exact resolve eq41 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1183
  have eq1203 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1200
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1200
    | exact resolve eq1200 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1200
  have eq1206 : x = (k (M.op x y) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1188 eq28
    | (have j0 := eq28 x x
       grind)
    | exact resolve eq28 eq1188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1240 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1203 eq1083
    | (have j0 := eq1083 (σ y)
       grind)
    | (have r₁ := eq1083 (σ y)
       have r₂ := eq1203
       grind)
    | exact resolve eq1083 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203
  have eq1241 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1240
  have eq1256 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1241 eq178
    | exact resolve eq178 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1259 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1241 eq182
    | exact resolve eq182 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq1264 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1241 eq597
    | exact resolve eq597 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597 eq1241
  have eq1268 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq1259
    | exact resolve eq1259 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259
  have eq1277 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1268 eq576
    | exact resolve eq576 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268
  have eq1493 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op X0 (σ y)) X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | exact superpose eq1264 eq16
    | exact resolve eq16 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1503 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op X0 (σ y)) X0) y) := by
    intro X0
    first
    | (have i₁ := eq1493 X0 x
       have i₂ := eq1177 (M.op (M.op X0 sF3) X0) x
       grind)
    | exact superpose eq1177 eq1493
    | exact resolve eq1493 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493
  have eq1513 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq1264 eq1503
    | exact resolve eq1503 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264 eq1503
  have eq3236 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1206 eq38
    | exact resolve eq38 eq1206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1206
  have eq3242 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3236
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3236
    | exact resolve eq3236 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3236
  have eq4224 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq3242 eq1033
    | (have j0 := eq1033 X0 (σ x) x
       grind)
    | exact resolve eq1033 eq3242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033
  have eq4225 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4224 x
       have i₂ := eq1177 (M.op sF1 sF2) x
       grind)
    | exact superpose eq1177 eq4224
    | exact resolve eq4224 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177 eq4224
  have eq4229 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4225
       have i₂ := eq1513 (M.op sF1 sF2)
       grind)
    | exact superpose eq1513 eq4225
    | exact resolve eq4225 eq1513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513 eq4225
  have eq4231 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq4229
    | (have j1 := eq28 x (σ x)
       grind)
    | exact resolve eq4229 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4229
  have eq4232 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3242 eq4231
    | exact resolve eq4231 eq3242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3242 eq4231
  have eq4233 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq4232
    | exact resolve eq4232 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4232
  have eq4234 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq4233
       have r₂ := eq27
       grind)
    | exact resolve eq4233 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4233
  have eq4753 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4234 eq1256
    | exact resolve eq1256 eq4234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4755 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq4753
    | exact resolve eq4753 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4753
  have eq4784 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4234 eq4755
    | exact resolve eq4755 eq4234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4234 eq4755
  have eq4829 : (k x x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq179 x
       have i₂ := eq4784
       grind)
    | exact superpose eq4784 eq179
    | exact resolve eq179 eq4784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4884 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4784 eq4829
    | exact resolve eq4829 eq4784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4784 eq4829
  have eq5143 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq4884
       grind)
    | exact superpose eq4884 eq40
    | exact resolve eq40 eq4884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq4884
  have eq5148 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5143
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5143
    | exact resolve eq5143 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5143
  have eq5594 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5148 eq1083
    | (have j0 := eq1083 (σ x)
       grind)
    | (have r₁ := eq1083 (σ x)
       have r₂ := eq5148
       grind)
    | exact resolve eq1083 eq5148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5148
  have eq5597 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5594
  have eq5873 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5597 eq1256
    | exact resolve eq1256 eq5597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256
  have eq5875 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5873
    | exact resolve eq5873 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq5873
  have eq5905 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5597 eq5875
    | exact resolve eq5875 eq5597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5597 eq5875
  have eq5906 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5905
  have eq5934 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq5906 eq27
    | exact resolve eq27 eq5906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq5937 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) := by
    first
    | exact superpose eq5906 eq576
    | exact resolve eq576 eq5906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq5942 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5906 eq1277
    | exact resolve eq1277 eq5906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277 eq5906
  have eq5951 : (σ x) = (k (M.op (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq5937
       have i₂ := eq179 sF2
       grind)
    | exact superpose eq179 eq5937
    | exact resolve eq5937 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq5937
  have eq5955 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq5942 eq5951
    | exact resolve eq5951 eq5942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5942 eq5951
  have eq6092 : (τ (σ x)) = (k (τ (σ x)) x) := by
    first
    | exact superpose eq5955 eq142
    | exact resolve eq142 eq5955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq5955
  have eq6100 : x = (k x x) := by
    first
    | exact superpose eq30 eq6092
    | exact resolve eq6092 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq6092
  have eq6174 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1083 x
       have i₂ := eq6100
       grind)
    | exact superpose eq6100 eq1083
    | (have j0 := eq1083 x
       grind)
    | (have r₁ := eq1083 x
       have r₂ := eq6100
       grind)
    | exact resolve eq1083 eq6100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083 eq6100
  have eq6177 : x = (M.op x x) := by grind
  clear eq6174
  have eq6225 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1172 x x
       have i₂ := eq6177
       grind)
    | exact superpose eq6177 eq1172
    | exact resolve eq1172 eq6177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq6229 : x = (M.op x y) := by
    first
    | (have i₁ := eq6225
       have i₂ := eq6177
       grind)
    | exact superpose eq6177 eq6225
    | exact resolve eq6225 eq6177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6177 eq6225
  have eq6258 : x = (M.op x y) := by
    first
    | (have i₁ := eq6229
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6229
    | exact resolve eq6229 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq6229
  have eq6309 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq6258
       grind)
    | exact superpose eq6258 eq22
    | exact resolve eq22 eq6258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6258
  have eq6365 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq6309 eq20
    | exact resolve eq20 eq6309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq6309
  have eq6383 : False := by grind
  exact eq6383

/-- `Equation1845`: `x = (x ◇ (x ◇ y)) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxy_pxx_pxy_Equation1845 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1845 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1845.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X2)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 (M.op X1 X1) X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
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
  have eq175 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, x = (M.op (M.op x (M.op x y)) (M.op X0 X0)) := by
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
  have eq177 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)) X2
       have i₂ := eq16 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 X0 X1 X2
       have i₂ := eq175 X2
       grind)
    | exact superpose eq175 eq179
    | exact resolve eq179 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq182 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq177 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq177
    | exact resolve eq177 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq183 : ∀ X0 : G, x = (M.op (M.op x (M.op x y)) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq176
    | exact resolve eq176 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq185 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 X2)) (k X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 : G, x = (M.op (M.op x (M.op x y)) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq183 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq183
    | exact resolve eq183 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 (M.op X0 X1)) (k X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq180 (M.op X0 (M.op X0 X1)) (M.op x x) X3
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq180
    | exact resolve eq180 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq644 : ∀ X1 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (k X1 X1)) := by
    intro X1
    first
    | exact superpose eq182 eq180
    | exact resolve eq180 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq645 : ∀ X1 : G, (M.op (M.op x (M.op x y)) x) = (M.op (M.op x (M.op x y)) (k X1 X1)) := by
    intro X1
    first
    | exact superpose eq183 eq180
    | exact resolve eq180 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq646 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq180 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq180
    | (have j0 := eq180 x y X0
       grind)
    | exact resolve eq180 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq647 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (k X0 X0)) := by
    intro X0
    first
    | exact superpose eq26 eq180
    | (have j0 := eq180 (σ x) (σ y) X0
       grind)
    | exact resolve eq180 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq183 eq645
    | exact resolve eq645 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq645
  have eq663 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq182 eq644
    | exact resolve eq644 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq644
  have eq668 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq639 X0 X1 x
       have i₂ := eq185 x X0 X1
       grind)
    | exact superpose eq185 eq639
    | exact resolve eq639 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq639
  have eq706 : ∀ X0 X1 : G, (M.op (M.op X0 (k X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq668 X0 x
       have i₂ := eq180 X0 x X1
       grind)
    | exact superpose eq180 eq668
    | exact resolve eq668 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq668
  have eq811 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (k X0 X1)) (M.op X2 X2)) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq832 : (M.op x y) = (k x y) ∨ y = (M.op y y) := by
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
  have eq840 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq851 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq840
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq840
    | exact resolve eq840 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq859 : (M.op x y) = (k x y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq832
       have i₂ := eq175 y
       grind)
    | exact superpose eq175 eq832
    | exact resolve eq832 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq880 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (k X0 X1)) (k X2 X2)) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq811 X0 X1 X2
       have i₂ := eq175 X2
       grind)
    | exact superpose eq175 eq811
    | (have j0 := eq811 X0 X1 X2
       grind)
    | exact resolve eq811 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq910 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (k X0 X1)) (k X2 X2)) = X0 ∨ (k X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq880 X0 X1 X2
       have i₂ := eq175 X1
       grind)
    | exact superpose eq175 eq880
    | (have j0 := eq880 X0 X1 X2
       grind)
    | exact resolve eq880 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq930 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq859
       grind)
    | exact superpose eq859 eq41
    | exact resolve eq41 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq931 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq930
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq930
    | exact resolve eq930 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq933 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq20 eq931
    | exact resolve eq931 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq936 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq933 eq851
    | exact resolve eq851 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851 eq933
  have eq943 : (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq936
       have r₂ := eq27
       grind)
    | exact resolve eq936 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq949 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (k y y) := by
    first
    | exact superpose eq943 eq153
    | exact resolve eq153 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq943
  have eq963 : y = (k y y) ∨ y = (k y y) := by
    first
    | exact superpose eq32 eq949
    | exact resolve eq949 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq949
  have eq964 : y = (k y y) := by grind
  clear eq963
  have eq971 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq964
       grind)
    | exact superpose eq964 eq41
    | exact resolve eq41 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq975 : x = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq190 y
       have i₂ := eq964
       grind)
    | exact superpose eq964 eq190
    | exact resolve eq190 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq978 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq646 y
       have i₂ := eq964
       grind)
    | exact superpose eq964 eq646
    | exact resolve eq646 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq981 : ∀ X0 : G, (M.op (M.op X0 y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq706 X0 y
       have i₂ := eq964
       grind)
    | exact superpose eq964 eq706
    | exact resolve eq706 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq983 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq978
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq978
    | exact resolve eq978 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq978
  have eq985 : x = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq975
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq975
    | exact resolve eq975 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq988 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq971
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq971
    | exact resolve eq971 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq971
  have eq990 : x = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq983 eq985
    | exact resolve eq985 eq983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq993 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq983 eq662
    | exact resolve eq662 eq983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662 eq983
  have eq1015 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq988 eq647
    | exact resolve eq647 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq1017 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq988 eq706
    | exact resolve eq706 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706 eq988
  have eq1019 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq1015
    | exact resolve eq1015 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015
  have eq1034 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) x) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq990 eq16
    | exact resolve eq16 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq1035 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) x) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1034 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq1034
    | exact resolve eq1034 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034
  have eq1040 : ∀ X0 : G, (M.op x y) = (M.op x (k X0 X0)) := by
    intro X0
    first
    | exact superpose eq993 eq1035
    | exact resolve eq1035 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035
  have eq1042 : x = (k (M.op x y) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq993 eq28
    | (have j0 := eq28 x x
       grind)
    | exact resolve eq28 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq1049 : x = (k (M.op x y) x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1042
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq1042
    | exact resolve eq1042 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq1053 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1019 eq663
    | exact resolve eq663 eq1019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663 eq1019
  have eq1069 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq1053 eq16
    | exact resolve eq16 eq1053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1070 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1069 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq1069
    | exact resolve eq1069 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq1075 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (k X0 X0)) := by
    intro X0
    first
    | exact superpose eq1053 eq1070
    | exact resolve eq1070 eq1053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053 eq1070
  have eq1165 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op (M.op X0 y) X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 y) X0 X1
       have i₂ := eq981 X0
       grind)
    | exact superpose eq981 eq16
    | exact resolve eq16 eq981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1167 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op (M.op X0 y) X0) (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1165 X0 X1
       have i₂ := eq175 X1
       grind)
    | exact superpose eq175 eq1165
    | exact resolve eq1165 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165
  have eq1175 : ∀ X0 X1 : G, (M.op X0 (k X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1167 X0 X1
       have i₂ := eq981 X0
       grind)
    | exact superpose eq981 eq1167
    | exact resolve eq1167 eq981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981 eq1167
  have eq1287 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op X0 (σ y)) X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | exact superpose eq1017 eq16
    | exact resolve eq16 eq1017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1290 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op X0 (σ y)) X0) (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1287 X0 X1
       have i₂ := eq175 X1
       grind)
    | exact superpose eq175 eq1287
    | exact resolve eq1287 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287
  have eq1298 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op X0 (σ y)) X0) y) := by
    intro X0
    first
    | (have i₁ := eq1290 X0 x
       have i₂ := eq1175 (M.op (M.op X0 sF3) X0) x
       grind)
    | exact superpose eq1175 eq1290
    | exact resolve eq1290 eq1175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq1302 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq1017 eq1298
    | exact resolve eq1298 eq1017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017 eq1298
  have eq1394 : ∀ X0 X1 X2 : G, (M.op (k X0 (k X0 X1)) (k X2 X2)) = X0 ∨ (k X1 X1) = X1 ∨ (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq910 X0 X1 X2
       have i₂ := eq28 X0 (k X0 X1)
       grind)
    | exact superpose eq28 eq910
    | (have j0 := eq910 X0 X1 X2
       have j1 := eq28 X0 (k X0 X1)
       grind)
    | exact resolve eq910 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq910
  have eq1424 : ∀ X0 X1 : G, (M.op (k X0 (k X0 X1)) y) = X0 ∨ (k X1 X1) = X1 ∨ (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1394 X0 X1 x
       have i₂ := eq1175 (k X0 (k X0 X1)) x
       grind)
    | exact superpose eq1175 eq1394
    | (have j0 := eq1394 X0 X1 x
       grind)
    | exact resolve eq1394 eq1175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175 eq1394
  have eq1429 : ∀ X0 X1 : G, (M.op (k X0 (k X0 X1)) (σ y)) = X0 ∨ (k X1 X1) = X1 ∨ (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1424 X0 X1
       have i₂ := eq1302 (k X0 (k X0 X1))
       grind)
    | exact superpose eq1302 eq1424
    | (have j0 := eq1424 X0 X1
       grind)
    | exact resolve eq1424 eq1302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302 eq1424
  have eq1434 : ∀ X0 X1 : G, (k X0 X1) = (k (k X0 X1) (k X0 X1)) ∨ (M.op (k X0 (k X0 X1)) (σ y)) = X0 ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1429 X0 X1
       have i₂ := eq175 (k X0 X1)
       grind)
    | exact superpose eq175 eq1429
    | (have j0 := eq1429 X0 X1
       grind)
    | exact resolve eq1429 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429
  have eq1860 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1075 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1075
    | exact resolve eq1075 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq5163 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq1049 eq38
    | exact resolve eq38 eq1049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1049
  have eq5174 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq5163
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5163
    | exact resolve eq5163 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5163
  have eq6701 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ x)) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq5174 eq1434
    | (have j0 := eq1434 x (σ x)
       grind)
    | exact resolve eq1434 eq5174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1434
  have eq6770 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ x)) (σ y)) ∨ x = (k x x) := by grind
  clear eq6701
  have eq6802 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq5174 eq6770
    | exact resolve eq6770 eq5174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5174 eq6770
  have eq6815 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq26 eq6802
    | exact resolve eq6802 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq6802
  have eq6819 : (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have r₁ := eq6815
       have r₂ := eq27
       grind)
    | exact resolve eq6815 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6815
  have eq7084 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k x x) := by
    first
    | exact superpose eq6819 eq142
    | exact resolve eq142 eq6819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq6819
  have eq7163 : x = (k x x) ∨ x = (k x x) := by
    first
    | exact superpose eq30 eq7084
    | exact resolve eq7084 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq7084
  have eq7164 : x = (k x x) := by grind
  clear eq7163
  have eq7182 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq7164
       grind)
    | exact superpose eq7164 eq40
    | exact resolve eq40 eq7164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7200 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1040 x
       have i₂ := eq7164
       grind)
    | exact superpose eq7164 eq1040
    | exact resolve eq1040 eq7164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq7213 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1860 x
       have i₂ := eq7164
       grind)
    | exact superpose eq7164 eq1860
    | exact resolve eq1860 eq7164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1860 eq7164
  have eq7242 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq7213
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7213
    | exact resolve eq7213 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7213
  have eq7254 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq7200
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq7200
    | exact resolve eq7200 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7200
  have eq7269 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq7182
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7182
    | exact resolve eq7182 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7182
  have eq7272 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq7242
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq7242
    | exact resolve eq7242 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq7242
  have eq7284 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7269 eq7272
    | exact resolve eq7272 eq7269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7272
  have eq7294 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq7284 eq27
    | exact resolve eq27 eq7284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq7284
  have eq7391 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq7254
       grind)
    | exact superpose eq7254 eq40
    | exact resolve eq40 eq7254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq7254
  have eq7484 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq7391
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7391
    | exact resolve eq7391 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq7391
  have eq7517 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq7269 eq7484
    | exact resolve eq7484 eq7269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7269 eq7484
  have eq7633 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq7517 eq20
    | exact resolve eq20 eq7517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq7517
  have eq7653 : False := by grind
  exact eq7653

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = m(Y,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_pyy_pxy_x_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq29 (σ X0)
       grind)
    | exact superpose eq29 eq15
    | exact resolve eq15 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq29 (τ X0)
       grind)
    | exact superpose eq29 eq17
    | exact resolve eq17 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32
    | exact resolve eq32 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0
       have i₂ := eq29 X0
       grind)
    | exact superpose eq29 eq31
    | exact resolve eq31 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq29 X0
       grind)
    | exact superpose eq29 eq33
    | exact resolve eq33 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq51 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq26 X0 X0
       grind)
    | exact superpose eq26 eq9
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq26 X1 X1
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq26
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq26 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq81 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq82 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq78 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq78 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq78 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq87 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq73 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq73 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq73 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq73 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq89 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq79 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq79 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq79 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq95 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq81 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq81 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq81 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq81 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq96 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 X1
       have i₂ := eq34 X1
       grind)
    | exact superpose eq34 eq58
    | (have j0 := eq58 X0 X1
       grind)
    | exact resolve eq58 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq100 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1
       have i₂ := eq29 X1
       grind)
    | exact superpose eq29 eq89
    | (have j0 := eq89 X0 X1
       grind)
    | exact resolve eq89 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq89
  have eq102 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       have j1 := eq82 X1 X0
       grind)
    | (have r₁ := eq95 X0 X0
       have r₂ := eq82 X0 X0
       grind)
    | (have r₁ := eq95 X1 X0
       have r₂ := eq82 X0 X1
       grind)
    | exact resolve eq95 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq95
  have eq128 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq142 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq102 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq102
    | exact resolve eq102 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq102 (τ X1) X0
       grind)
    | exact superpose eq102 eq18
    | (have j1 := eq102 (τ X1) X0
       grind)
    | exact resolve eq18 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq147 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq102 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq170 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq223 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq100 (σ X0) (σ X1)
       grind)
    | exact superpose eq100 eq15
    | (have j1 := eq100 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq223 X0 X1
       have i₂ := eq34 X1
       grind)
    | exact superpose eq34 eq223
    | (have j0 := eq223 X0 X1
       grind)
    | exact resolve eq223 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq242 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ (M.op X0 X0))) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq9
    | exact resolve eq9 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq128 X0 X1
       have i₂ := eq100 (σ X0) X1
       grind)
    | exact superpose eq100 eq128
    | (have j1 := eq100 (σ X0) X1
       grind)
    | exact resolve eq128 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq517 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op (M.op X4 X1) (M.op X4 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X4 X1) X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq23 X1 X4 X0 X2
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1227 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ X1)) = (M.op (σ X1) (σ X2)) ∨ (σ (M.op X0 X1)) = (M.op (σ X2) (σ X1)) ∨ (M.op (σ X2) (σ X1)) = (σ (k X2 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq96 X2 X1
       have i₂ := eq100 X0 X1
       grind)
    | (have i₁ := eq96 X0 X1
       have i₂ := eq100 X1 X1
       grind)
    | exact superpose eq100 eq96
    | (have j0 := eq96 X2 X1
       have j1 := eq100 X0 X1
       grind)
    | exact resolve eq96 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq100
  have eq1859 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1 (M.op X0 X0)
       have i₂ := eq26 X0 X0
       grind)
    | exact superpose eq26 eq51
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1863 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq23 X1 X1 X0 X2
       grind)
    | exact superpose eq23 eq51
    | exact resolve eq51 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq2227 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq143 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq143
    | exact resolve eq143 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq2296 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2227 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2227
    | (have j0 := eq2227 X0 X1
       grind)
    | exact resolve eq2227 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227
  have eq2331 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 (M.op X3 X0)) (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1863 X3 (M.op X1 X0) (M.op X0 X0) X2
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq1863
    | exact resolve eq1863 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2377 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1863 (M.op X0 X1) X0 X1 (M.op X0 X1)
       have i₂ := eq24 (M.op X0 X1)
       grind)
    | exact superpose eq24 eq1863
    | exact resolve eq1863 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2594 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2377 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq2377
    | exact resolve eq2377 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2711 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq142 x y
       grind)
    | exact superpose eq142 eq16
    | (have j1 := eq142 x y
       grind)
    | exact resolve eq16 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq3689 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq517 (M.op X0 X1) X0 X1 (M.op X0 X1) X2
       have i₂ := eq24 (M.op X0 X1)
       grind)
    | exact superpose eq24 eq517
    | exact resolve eq517 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq3845 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op X0 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3689 X0 X1 X2
       have i₂ := eq2594 X0 X2
       grind)
    | exact superpose eq2594 eq3689
    | exact resolve eq3689 eq2594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3689
  have eq4347 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3845 X0 (M.op X0 X0) X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq3845
    | exact resolve eq3845 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4433 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 X2 X1 X1
       have i₂ := eq3845 X1 (M.op X0 X1) X0
       grind)
    | exact superpose eq3845 eq23
    | exact resolve eq23 eq3845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3845
  have eq4778 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq231 x y
       grind)
    | exact superpose eq231 eq16
    | (have j1 := eq231 x y
       grind)
    | exact resolve eq16 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq5063 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X1)) (M.op X1 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (M.op X1 (M.op X0 X1))
       have i₂ := eq4347 X1 X0
       grind)
    | exact superpose eq4347 eq9
    | exact resolve eq9 eq4347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4347
  have eq5568 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) = (M.op (M.op X3 (M.op X4 X0)) (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1863 X4 (M.op X1 (M.op X2 X0)) (M.op X0 X0) X3
       have i₂ := eq5063 X2 X0 X1
       grind)
    | exact superpose eq5063 eq1863
    | exact resolve eq1863 eq5063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1863
  have eq5570 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) = (M.op X0 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2377 (M.op X1 (M.op X2 X0)) (M.op X0 X0)
       have i₂ := eq5063 X2 X0 X1
       grind)
    | exact superpose eq5063 eq2377
    | exact resolve eq2377 eq5063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5063
  have eq5580 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X2 X0))) = (M.op X0 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5570 X0 X1 X2
       have i₂ := eq2594 (M.op X2 X0) X1
       grind)
    | exact superpose eq2594 eq5570
    | exact resolve eq5570 eq2594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5570
  have eq5581 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X2 X0))) = (M.op (M.op X3 (M.op X4 X0)) (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5568 X0 X1 X2 X3 X4
       have i₂ := eq2594 (M.op X2 X0) X1
       grind)
    | exact superpose eq2594 eq5568
    | exact resolve eq5568 eq2594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5568
  have eq5608 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X4 X0)) (M.op X1 (M.op X2 X0))) = (M.op X0 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5581 X0 X1 X2 X3 X4
       have i₂ := eq5580 X0 X1 X2
       grind)
    | exact superpose eq5580 eq5581
    | exact resolve eq5581 eq5580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5580 eq5581
  have eq5820 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4433 (M.op X0 X0) X1 X0
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq4433
    | exact resolve eq4433 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4433
  have eq34160 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) (M.op X0 (M.op X1 X2))) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5820 X0 (M.op (M.op X2 (M.op X0 x)) (M.op X2 (M.op X0 x)))
       have i₂ := eq23 X0 X0 X2 x
       grind)
    | exact superpose eq23 eq5820
    | exact resolve eq5820 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq5820
  have eq34663 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34160 X0 X1 X2
       have i₂ := eq2331 (M.op X1 X2) X0 (M.op X0 (M.op X1 X2)) X0
       grind)
    | exact superpose eq2331 eq34160
    | exact resolve eq34160 eq2331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2331 eq34160
  have eq34729 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X2))) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34663 X0 X1 X2
       have i₂ := eq5608 X2 X0 X1 X0 X1
       grind)
    | exact superpose eq5608 eq34663
    | exact resolve eq34663 eq5608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5608 eq34663
  have eq59702 : ∀ X0 X1 X2 : G, (σ (M.op X1 X2)) = (M.op X0 (σ X2)) ∨ (M.op (σ X2) X0) = (M.op X0 (σ X2)) ∨ (σ (k (τ X0) X2)) = (M.op X0 (σ X2)) ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1227 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1227
    | (have j0 := eq1227 X1 X2 X2
       grind)
    | exact resolve eq1227 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq60494 : ∀ X0 X1 X2 : G, (M.op X0 (σ X2)) = (k X0 (σ X2)) ∨ (σ (M.op X1 X2)) = (M.op X0 (σ X2)) ∨ (M.op (σ X2) X0) = (M.op X0 (σ X2)) ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59702 X0 X1 X2
       have i₂ := eq17 X0 X2
       grind)
    | exact superpose eq17 eq59702
    | (have j0 := eq59702 X0 X1 X2
       grind)
    | exact resolve eq59702 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq59702
  have eq60628 : ∀ X0 X1 X2 : G, (σ (M.op X1 X2)) = (M.op X0 (σ X2)) ∨ (M.op X0 (σ X2)) = (k X0 (σ X2)) ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq60494 X0 X1 X2
       have j1 := eq12 X0 (σ X2)
       grind)
    | (have r₁ := eq60494 X1 X1 X2
       have r₂ := eq12 (σ X2) X1
       grind)
    | (have r₁ := eq60494 X0 X1 X2
       have r₂ := eq12 X0 (σ X2)
       grind)
    | exact resolve eq60494 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60494
  have eq73912 : ∀ X0 X1 X2 : G, (σ (M.op X1 X0)) = (M.op (M.op X2 (σ X0)) (σ X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq242 (M.op X0 X1) X1
       have i₂ := eq87 X0 X1 X0
       grind)
    | exact superpose eq87 eq242
    | (have j1 := eq87 X1 X0 X2
       grind)
    | exact resolve eq242 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq242
  have eq74253 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq73912 X0 X1 x
       have i₂ := eq1859 (σ X0) x
       grind)
    | exact superpose eq1859 eq73912
    | (have j0 := eq73912 X0 X1 x
       grind)
    | exact resolve eq73912 eq1859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73912
  have eq74344 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq74253 X0 X1
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq74253
    | (have j0 := eq74253 X0 X1
       grind)
    | exact resolve eq74253 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74253
  have eq78868 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq2711
       have i₂ := eq2296 y x
       grind)
    | exact superpose eq2296 eq2711
    | (have j1 := eq2296 y x
       grind)
    | (have r₁ := eq2711
       have r₂ := eq2296 y x
       grind)
    | exact resolve eq2711 eq2296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2296 eq2711
  have eq78869 : (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by grind
  clear eq78868
  have eq79770 : (M.op x y) = (τ (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq78869
       grind)
    | exact superpose eq78869 eq10
    | exact resolve eq10 eq78869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78869
  have eq79859 : x = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq79770
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq79770
    | exact resolve eq79770 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79770
  have eq79861 : x = (k x y) := by
    first
    | (have j1 := eq147 x y
       grind)
    | (have r₁ := eq79859
       have r₂ := eq147 x y
       grind)
    | exact resolve eq79859 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq79859
  have eq138176 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq369 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq369
    | exact resolve eq369 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq139625 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq138176 X0 X1
       have i₂ := eq170 X1 X0
       grind)
    | exact superpose eq170 eq138176
    | (have j0 := eq138176 X0 X1
       grind)
    | exact resolve eq138176 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq138176
  have eq139851 : (τ (M.op x y)) = (τ x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq139625 x y
       have i₂ := eq79861
       grind)
    | exact superpose eq79861 eq139625
    | (have j0 := eq139625 x y
       grind)
    | exact resolve eq139625 eq79861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139625
  have eq141916 : (M.op (M.op x y) (M.op x y)) = (σ (M.op (τ x) (τ x))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq36 (M.op x y)
       have i₂ := eq139851
       grind)
    | exact superpose eq139851 eq36
    | exact resolve eq36 eq139851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139851
  have eq141989 : (M.op (M.op x y) (M.op x y)) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq141916
       have i₂ := eq36 x
       grind)
    | exact superpose eq36 eq141916
    | exact resolve eq141916 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq141916
  have eq141994 : (M.op y (M.op x y)) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq141989
       have i₂ := eq2594 y x
       grind)
    | exact superpose eq2594 eq141989
    | exact resolve eq141989 eq2594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2594 eq141989
  have eq188797 : (M.op y (M.op x x)) = (M.op x (M.op x x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq34729 y x y
       have i₂ := eq141994
       grind)
    | exact superpose eq141994 eq34729
    | exact resolve eq34729 eq141994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34729 eq141994
  have eq189120 : x = (M.op y (M.op x x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq188797
       have i₂ := eq24 x
       grind)
    | exact superpose eq24 eq188797
    | exact resolve eq188797 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq188797
  have eq191025 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2377 y (M.op x x)
       have i₂ := eq189120
       grind)
    | exact superpose eq189120 eq2377
    | exact resolve eq2377 eq189120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2377 eq189120
  have eq191112 : (M.op x y) = (M.op y y) := by grind
  clear eq191025
  have eq191711 : ∀ X0 : G, (σ (M.op x y)) = (σ (M.op X0 y)) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq74344 y X0
       have i₂ := eq191112
       grind)
    | exact superpose eq191112 eq74344
    | (have j0 := eq74344 y X0
       grind)
    | exact resolve eq74344 eq191112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74344
  have eq402051 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op X0 y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq60628 (σ x) X0 y
       grind)
    | exact superpose eq60628 eq16
    | (have j1 := eq60628 (σ x) X0 y
       grind)
    | (have r₁ := eq16
       have r₂ := eq60628 (σ x) x y
       grind)
    | exact resolve eq16 eq60628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60628
  have eq402243 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq402051 X0
       have j1 := eq191711 X0
       grind)
    | (have r₁ := eq402051 X0
       have r₂ := eq191711 X0
       grind)
    | (have r₁ := eq402051 x
       have r₂ := eq191711 x
       grind)
    | exact resolve eq402051 eq191711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191711 eq402051
  have eq402686 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq402243 X0
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq402243
    | (have j0 := eq402243 X0
       grind)
    | exact resolve eq402243 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402243
  have eq402883 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq402686 X0
       have i₂ := eq79861
       grind)
    | exact superpose eq79861 eq402686
    | (have j0 := eq402686 X0
       grind)
    | exact resolve eq402686 eq79861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79861 eq402686
  have eq403207 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq1859 (σ y) (σ x)
       have i₂ := eq402883 X0
       grind)
    | exact superpose eq402883 eq1859
    | (have j1 := eq402883 X0
       grind)
    | exact resolve eq1859 eq402883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1859 eq402883
  have eq403470 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq403207 X0
       have i₂ := eq34 y
       grind)
    | exact superpose eq34 eq403207
    | (have j0 := eq403207 X0
       grind)
    | exact resolve eq403207 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq403207
  have eq403674 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq403470 X0
       have i₂ := eq191112
       grind)
    | exact superpose eq191112 eq403470
    | (have j0 := eq403470 X0
       grind)
    | exact resolve eq403470 eq191112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403470
  have eq403768 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq403674 X0
       grind)
    | (have r₁ := eq403674 X0
       have r₂ := eq16
       grind)
    | exact resolve eq403674 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403674
  have eq405116 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4778
       have i₂ := eq403768 x
       grind)
    | exact superpose eq403768 eq4778
    | exact resolve eq4778 eq403768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4778 eq403768
  have eq405121 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq405116
  have eq405123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq405121
       have i₂ := eq191112
       grind)
    | exact superpose eq191112 eq405121
    | exact resolve eq405121 eq191112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191112 eq405121
  have eq405144 : False := by grind
  exact eq405144
