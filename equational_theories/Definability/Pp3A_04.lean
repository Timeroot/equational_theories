import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxx_pyy_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq70 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq78 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
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
  clear eq44
  have eq85 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq78
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq79
    | exact resolve eq79 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq87
    | exact resolve eq87 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq96 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq96
  have eq129 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq146 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq129
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq129
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq129 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq129 eq16
    | exact resolve eq16 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq146
  have eq167 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq189 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq204 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq206 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 X0) x) := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
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
  have eq345 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X1 X2)) = (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) := by
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
  have eq354 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X0 X1) X0) := by
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
  have eq357 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = X1 := by
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
  have eq378 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq209 sF2
       have i₂ := eq53 sF2 x sF2
       grind)
    | (have i₁ := eq209 x
       have i₂ := eq53 sF2 x x
       grind)
    | exact superpose eq53 eq209
    | exact resolve eq209 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq834 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq354 sF4
       have i₂ := eq53 sF4 x sF2
       grind)
    | exact superpose eq53 eq354
    | exact resolve eq354 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1073 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq342 X3 X1 x
       have i₂ := eq342 X0 X1 x
       grind)
    | (have i₁ := eq342 X0 X1 X3
       have i₂ := eq342 (M.op X3 X3) X1 X3
       grind)
    | exact superpose eq342 eq342
    | exact resolve eq342 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1084 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X1))) = (M.op (M.op X2 X2) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq342 X0 (M.op X1 X1) X3
       have i₂ := eq342 X0 X1 X1
       grind)
    | (have i₁ := eq342 X0 (M.op X1 X1) X3
       have i₂ := eq342 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq342 eq342
    | exact resolve eq342 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1111 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X2 X3) X2)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) X3
       have i₂ := eq342 X0 X1 X1
       grind)
    | (have i₁ := eq14 X0 (M.op X1 X1) X2
       have i₂ := eq342 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq342 eq14
    | exact resolve eq14 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1112 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op X1 X1)
       have i₂ := eq342 X0 X1 X1
       grind)
    | (have i₁ := eq50 (M.op X1 X1)
       have i₂ := eq342 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq342 eq50
    | exact resolve eq50 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1113 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X1)
       have i₂ := eq342 X0 X1 X1
       grind)
    | (have i₁ := eq51 (M.op X1 X1)
       have i₂ := eq342 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq342 eq51
    | exact resolve eq51 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1119 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 (M.op X1 X1)) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq209 (M.op X1 X1)
       have i₂ := eq342 X0 X1 X1
       grind)
    | (have i₁ := eq209 (M.op X1 X1)
       have i₂ := eq342 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq342 eq209
    | exact resolve eq209 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1169 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1084 X0 X1 x X3
       have i₂ := eq52 X0 x X1
       grind)
    | exact superpose eq52 eq1084
    | exact resolve eq1084 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1084
  have eq1186 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) = (M.op (M.op X1 X1) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq834 eq53
    | exact resolve eq53 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq834
  have eq1190 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1186 X0 x
       have i₂ := eq357 X0 sF4 x
       grind)
    | exact superpose eq357 eq1186
    | exact resolve eq1186 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq1198 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1190 sF4
       have i₂ := eq356 sF4 x sF4
       grind)
    | (have i₁ := eq1190 sF4
       have i₂ := eq356 sF4 sF4 x
       grind)
    | exact superpose eq356 eq1190
    | exact resolve eq1190 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356 eq1190
  have eq3480 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (M.op X2 X2) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq354 eq345
    | exact resolve eq345 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq354
  have eq3697 : ∀ X1 X2 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op X2 X2) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ x)) := by
    intro X1 X2
    first
    | exact superpose eq209 eq3480
    | exact resolve eq3480 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq3480
  have eq4651 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq167 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq167
    | (have j0 := eq167 x
       grind)
    | exact resolve eq167 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq4662 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4651
  have eq4666 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4662
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq4662
    | exact resolve eq4662 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq4662
  have eq4682 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq4666
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq4666 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4666
  have eq4688 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq4682 eq49
    | exact resolve eq49 eq4682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq4901 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq189 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq189
    | (have j0 := eq189 y
       grind)
    | exact resolve eq189 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq4911 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq4901
  have eq4914 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4911
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq4911
    | exact resolve eq4911 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4911
  have eq4937 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq4914
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq4914 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4914
  have eq4952 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq4937 eq101
    | exact resolve eq101 eq4937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq5149 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq204
    | (have j0 := eq204 (M.op x y)
       grind)
    | exact resolve eq204 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq5158 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq5149
  have eq5160 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq129 eq5158
    | exact resolve eq5158 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5158
  have eq5190 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq5160
       have r₂ := eq13 x (σ (M.op x y))
       grind)
    | exact resolve eq5160 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5160
  have eq5215 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq5190 eq152
    | exact resolve eq152 eq5190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq12162 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4682 eq85
    | exact resolve eq85 eq4682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq4682
  have eq12434 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4937 eq102
    | exact resolve eq102 eq4937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq13767 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5190 eq153
    | exact resolve eq153 eq5190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq17355 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq12162
       grind)
    | exact superpose eq12162 eq16
    | exact resolve eq16 eq12162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12162
  have eq17406 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4688 eq17355
    | exact resolve eq17355 eq4688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17355
  have eq17409 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq17406
       have r₂ := eq13 x x
       grind)
    | exact resolve eq17406 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17406
  have eq18165 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq12434
       grind)
    | exact superpose eq12434 eq16
    | exact resolve eq16 eq12434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12434
  have eq18220 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4952 eq18165
    | exact resolve eq18165 eq4952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18165
  have eq18223 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq18220
       have r₂ := eq13 x y
       grind)
    | exact resolve eq18220 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18220
  have eq18224 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq18223
       grind)
    | exact superpose eq18223 eq70
    | exact resolve eq70 eq18223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq18264 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq4937 eq18224
    | exact resolve eq18224 eq4937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4937 eq18224
  have eq19119 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq13767 eq16
    | exact resolve eq16 eq13767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13767
  have eq19178 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5215 eq19119
    | exact resolve eq19119 eq5215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5215 eq19119
  have eq19181 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq19178
       have r₂ := eq13 x (M.op x y)
       grind)
    | exact resolve eq19178 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19178
  have eq19182 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq19181 eq129
    | exact resolve eq129 eq19181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq19181
  have eq19222 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq5190 eq19182
    | exact resolve eq19182 eq5190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5190 eq19182
  have eq24509 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq88 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq24510 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq24509
    | exact resolve eq24509 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24509
  have eq24521 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq24510
       have r₂ := eq27
       grind)
    | exact resolve eq24510 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24510
  have eq24525 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq24521 eq4952
    | exact resolve eq4952 eq24521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24521
  have eq24607 : (τ (σ y)) = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq24525
       have i₂ := eq18223
       grind)
    | exact superpose eq18223 eq24525
    | exact resolve eq24525 eq18223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24525
  have eq24616 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq24607
    | exact resolve eq24607 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24607
  have eq24617 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq24616
  have eq24620 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ y) (σ y))) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq24617 eq14
    | exact resolve eq14 eq24617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24703 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq24620 eq1113
    | exact resolve eq1113 eq24620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113
  have eq24706 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq24620 eq1119
    | exact resolve eq1119 eq24620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119
  have eq24749 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq24620 eq1073
    | exact resolve eq1073 eq24620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24620
  have eq25012 : (σ x) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq24706 eq24703
    | exact resolve eq24703 eq24706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24703 eq24706
  have eq25027 : (σ x) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq25012
  have eq25868 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq24749
    | (have j0 := eq24749 (σ x) X0
       grind)
    | exact resolve eq24749 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24749
  have eq27364 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq24617 eq25027
    | exact resolve eq25027 eq24617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24617 eq25027
  have eq27379 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq27364
  have eq27402 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27379 eq25868
    | exact resolve eq25868 eq27379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25868 eq27379
  have eq27474 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq27402
  have eq27518 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18264
       have i₂ := eq27474
       grind)
    | exact superpose eq27474 eq18264
    | exact resolve eq18264 eq27474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27552 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq1073 X0 y x
       have i₂ := eq27474
       grind)
    | exact superpose eq27474 eq1073
    | exact resolve eq1073 eq27474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27474
  have eq27589 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq27518
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27518
    | exact resolve eq27518 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27518
  have eq27651 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq27589 eq1073
    | exact resolve eq1073 eq27589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27589
  have eq28626 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq27552 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq27552
    | (have j0 := eq27552 x X0
       grind)
    | exact resolve eq27552 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27552
  have eq29030 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18264
       have i₂ := eq28626 y
       grind)
    | exact superpose eq28626 eq18264
    | exact resolve eq18264 eq28626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28626
  have eq29058 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq29030
    | exact resolve eq29030 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29030
  have eq30350 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq27651
    | (have j0 := eq27651 (σ x) X0
       grind)
    | exact resolve eq27651 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27651
  have eq30881 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30350 eq29058
    | exact resolve eq29058 eq30350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29058 eq30350
  have eq30884 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq30881
  have eq30914 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq30884
       have r₂ := eq27
       grind)
    | exact resolve eq30884 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30884
  have eq30926 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq30914
       grind)
    | exact superpose eq30914 eq14
    | exact resolve eq14 eq30914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30914
  have eq30996 : ∀ X0 : G, y = (M.op X0 (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq30926 x
       have i₂ := eq342 X0 y x
       grind)
    | (have i₁ := eq30926 X0
       have i₂ := eq342 (M.op X0 X0) y x
       grind)
    | exact superpose eq342 eq30926
    | exact resolve eq30926 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq31095 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1073 X0 (M.op y y) x
       have i₂ := eq30926 y
       grind)
    | exact superpose eq30926 eq1073
    | exact resolve eq1073 eq30926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30926
  have eq31689 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq31095 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq31095
    | (have j0 := eq31095 x X0
       grind)
    | exact resolve eq31095 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31095
  have eq32156 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18264
       have i₂ := eq31689 y
       grind)
    | exact superpose eq31689 eq18264
    | exact resolve eq18264 eq31689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18264
  have eq32165 : ∀ X0 : G, y = (M.op X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq30996 X0
       have i₂ := eq31689 y
       grind)
    | exact superpose eq31689 eq30996
    | exact resolve eq30996 eq31689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30996 eq31689
  have eq32174 : ∀ X0 : G, y = (M.op X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq32165 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32165
  have eq32193 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq32156
    | exact resolve eq32156 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32156
  have eq32333 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32174 eq19222
    | exact resolve eq19222 eq32174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19222 eq32174
  have eq32350 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32333
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32333
    | exact resolve eq32333 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq32333
  have eq32446 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op X0 (M.op X1 (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq32193 eq1169
    | exact resolve eq1169 eq32193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169 eq32193
  have eq38061 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq32350 eq32446
    | exact resolve eq32446 eq32350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32350 eq32446
  have eq38257 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq38061 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38061
  have eq38423 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38257 eq26
    | (have j1 := eq38257 (σ x)
       grind)
    | exact resolve eq26 eq38257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38257
  have eq38467 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq38423
       have r₂ := eq27
       grind)
    | exact resolve eq38423 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38423
  have eq38481 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq38467 eq27
    | exact resolve eq27 eq38467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq38492 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op (σ x) X0) (σ x))) := by
    intro X0
    first
    | exact superpose eq38467 eq1198
    | exact resolve eq1198 eq38467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq38495 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ x)) X1)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq38467 eq3697
    | exact resolve eq3697 eq38467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3697
  have eq38506 : ∀ X1 : G, (M.op (σ x) (σ x)) = (M.op X1 (σ x)) := by
    intro X1
    first
    | (have i₁ := eq38495 x X1
       have i₂ := eq357 sF2 X1 x
       grind)
    | exact superpose eq357 eq38495
    | exact resolve eq38495 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq38495
  have eq38507 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq378 eq38492
    | (have j0 := eq38492 (σ y)
       grind)
    | exact resolve eq38492 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq38492
  have eq38513 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq38467 eq38507
    | exact resolve eq38507 eq38467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38507
  have eq38548 : ∀ X0 : G, (k x x) = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq38506 eq4688
    | exact resolve eq4688 eq38506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4688 eq38506
  have eq38770 : ∀ X0 : G, (M.op x x) = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq38548 X0
       have i₂ := eq17409
       grind)
    | exact superpose eq17409 eq38548
    | exact resolve eq38548 eq17409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17409 eq38548
  have eq38792 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq38513
       have i₂ := eq1073 sF2 sF2 x
       grind)
    | (have i₁ := eq38513
       have i₂ := eq1073 X0 sF2 sF2
       grind)
    | exact superpose eq1073 eq38513
    | exact resolve eq38513 eq1073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq38800 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq38513 eq1111
    | exact resolve eq1111 eq38513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111
  have eq38801 : x = (M.op (σ x) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq38513 eq1112
    | exact resolve eq1112 eq38513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112 eq38513
  have eq43171 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq38792 eq38800
    | exact resolve eq38800 eq38792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43544 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq43171
    | (have j0 := eq43171 (σ y)
       grind)
    | exact resolve eq43171 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq43641 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq38467 eq43544
    | exact resolve eq43544 eq38467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38467 eq43544
  have eq44059 : ∀ X0 : G, (σ x) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq43641 eq38792
    | exact resolve eq38792 eq43641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38792
  have eq44069 : (τ (σ y)) = (M.op x x) := by
    first
    | exact superpose eq43641 eq38770
    | exact resolve eq38770 eq43641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38770 eq43641
  have eq44168 : y = (M.op x x) := by
    first
    | exact superpose eq29 eq44069
    | exact resolve eq44069 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq44069
  have eq44914 : (τ (σ x)) = (k y y) := by
    first
    | exact superpose eq44059 eq4952
    | exact resolve eq4952 eq44059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4952 eq44059
  have eq44946 : (τ (σ x)) = (M.op y y) := by
    first
    | (have i₁ := eq44914
       have i₂ := eq18223
       grind)
    | exact superpose eq18223 eq44914
    | exact resolve eq44914 eq18223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18223 eq44914
  have eq44978 : x = (M.op y y) := by
    first
    | exact superpose eq28 eq44946
    | exact resolve eq44946 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq44946
  have eq45869 : (M.op (M.op x y) x) = (M.op x x) := by
    first
    | (have i₁ := eq206 y
       have i₂ := eq44978
       grind)
    | exact superpose eq44978 eq206
    | exact resolve eq206 eq44978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq45948 : y = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq38800 y y
       have i₂ := eq44978
       grind)
    | exact superpose eq44978 eq38800
    | exact resolve eq38800 eq44978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38800 eq44978
  have eq45950 : y = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq45948
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq45948
    | exact resolve eq45948 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq45948
  have eq45994 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq45869
       have i₂ := eq44168
       grind)
    | exact superpose eq44168 eq45869
    | exact resolve eq45869 eq44168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44168 eq45869
  have eq46034 : (M.op x y) = (M.op (σ x) y) := by
    first
    | exact superpose eq45950 eq43171
    | exact resolve eq43171 eq45950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43171 eq45950
  have eq46103 : x = (M.op (σ x) y) := by
    first
    | exact superpose eq45994 eq38801
    | exact resolve eq38801 eq45994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38801 eq45994
  have eq46341 : x = (M.op x y) := by
    first
    | exact superpose eq46034 eq46103
    | exact resolve eq46103 eq46034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46034 eq46103
  have eq46342 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq46341 eq20
    | exact resolve eq20 eq46341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq46341
  have eq46555 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq46342
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq46342
    | exact resolve eq46342 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq46342
  have eq46616 : False := by grind
  exact eq46616

/-- `Equation1845`: `x = (x ◇ (x ◇ y)) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_y_pxy_pxx_pxy_Equation1845 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1845 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1845.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  clear eq40
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
  have eq182 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq548 : ∀ X1 : G, (M.op (M.op x (M.op x y)) x) = (M.op (M.op x (M.op x y)) (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq175 eq178
    | exact resolve eq178 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X3 X3)) := by
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
  have eq562 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 X0 X1 x
       have i₂ := eq178 X0 X2 x
       grind)
    | (have i₁ := eq178 X1 X1 X1
       have i₂ := eq178 X1 X1 X2
       grind)
    | exact superpose eq178 eq178
    | exact resolve eq178 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq175 eq548
    | exact resolve eq548 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq548
  have eq900 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (k X0 X1)) (M.op X2 X2)) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq933 : (M.op x y) = (k x y) ∨ y = (M.op y y) := by
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
  have eq940 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq944 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq950 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq933
       grind)
    | exact superpose eq933 eq41
    | exact resolve eq41 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933
  have eq951 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq950
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq950
    | exact resolve eq950 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq953 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq951
    | exact resolve eq951 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq963 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq953 eq940
    | exact resolve eq940 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940 eq953
  have eq970 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq963
       have r₂ := eq27
       grind)
    | exact resolve eq963 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq975 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq970 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq970
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq970
       grind)
    | exact resolve eq13 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq992 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq975
  have eq998 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq992 eq153
    | exact resolve eq153 eq992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq992
  have eq1001 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq32 eq998
    | exact resolve eq998 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq998
  have eq1004 : y = (M.op y y) := by
    first
    | (have j1 := eq944 y
       grind)
    | (have r₁ := eq1001
       have r₂ := eq944 y
       grind)
    | exact resolve eq1001 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq1008 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1004
       grind)
    | exact superpose eq1004 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq1004
       grind)
    | exact resolve eq13 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1018 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1 y
       have i₂ := eq1004
       grind)
    | exact superpose eq1004 eq178
    | exact resolve eq178 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1019 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq182 y
       have i₂ := eq1004
       grind)
    | exact superpose eq1004 eq182
    | exact resolve eq182 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1020 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq185 y
       have i₂ := eq1004
       grind)
    | exact superpose eq1004 eq185
    | exact resolve eq185 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1022 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq554 X0 X1 y
       have i₂ := eq1004
       grind)
    | exact superpose eq1004 eq554
    | exact resolve eq554 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq1004
  have eq1025 : y = (k y y) := by grind
  clear eq1008
  have eq1026 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1019
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1019
    | exact resolve eq1019 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1019
  have eq1031 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq1025
       grind)
    | exact superpose eq1025 eq41
    | exact resolve eq41 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1025
  have eq1034 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1031
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1031
    | exact resolve eq1031 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1031
  have eq1038 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1026 eq585
    | exact resolve eq585 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq1041 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1026 eq13
    | (have j0 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq1026
       grind)
    | exact resolve eq13 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1048 : (k (M.op x y) x) = (M.op (M.op x y) x) := by grind
  clear eq1041
  have eq1053 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1034 eq944
    | (have j0 := eq944 (σ y)
       grind)
    | (have r₁ := eq944 (σ y)
       have r₂ := eq1034
       grind)
    | exact resolve eq944 eq1034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034
  have eq1054 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1053
  have eq1112 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1054 eq185
    | exact resolve eq185 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq1054
  have eq1118 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq1112
    | exact resolve eq1112 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1112
  have eq1237 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq1020 eq1118
    | exact resolve eq1118 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020 eq1118
  have eq1348 : x = (k (M.op x y) x) := by
    first
    | exact superpose eq1048 eq1038
    | exact resolve eq1038 eq1048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038 eq1048
  have eq1551 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1348 eq38
    | exact resolve eq38 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1348
  have eq1556 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq1551
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1551
    | exact resolve eq1551 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551
  have eq1562 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq1556 eq900
    | (have j0 := eq900 X0 (σ x) x
       grind)
    | exact resolve eq900 eq1556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq1563 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1562 x
       have i₂ := eq1022 (M.op sF1 sF2) x
       grind)
    | exact superpose eq1022 eq1562
    | exact resolve eq1562 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022 eq1562
  have eq1567 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ x)) y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq28 eq1563
    | (have j1 := eq28 x (σ x)
       grind)
    | exact resolve eq1563 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1563
  have eq1569 : (σ (M.op x y)) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1556 eq1567
    | exact resolve eq1567 eq1556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1556 eq1567
  have eq1570 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1237 eq1569
    | exact resolve eq1569 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569
  have eq1571 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq1570
       have r₂ := eq27
       grind)
    | exact resolve eq1570 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1570
  have eq1585 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1571 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq1571
       grind)
    | exact resolve eq13 eq1571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1589 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq1571 eq562
    | exact resolve eq562 eq1571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq1592 : (σ x) = (k (σ x) (σ x)) := by grind
  clear eq1585
  have eq1596 : (M.op (σ x) (σ x)) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq1589 x
       have i₂ := eq1018 sF2 x
       grind)
    | exact superpose eq1018 eq1589
    | exact resolve eq1589 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018 eq1589
  have eq1606 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1237 eq1596
    | exact resolve eq1596 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237 eq1596
  have eq1610 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1571 eq1606
    | exact resolve eq1606 eq1571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1571 eq1606
  have eq1612 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1610 eq27
    | exact resolve eq27 eq1610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1610
  have eq1629 : (τ (σ x)) = (k (τ (σ x)) x) := by
    first
    | exact superpose eq1592 eq142
    | exact resolve eq142 eq1592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq1592
  have eq1634 : x = (k x x) := by
    first
    | exact superpose eq30 eq1629
    | exact resolve eq1629 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1629
  have eq1712 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq944 x
       have i₂ := eq1634
       grind)
    | exact superpose eq1634 eq944
    | (have j0 := eq944 x
       grind)
    | (have r₁ := eq944 x
       have r₂ := eq1634
       grind)
    | exact resolve eq944 eq1634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944 eq1634
  have eq1714 : x = (M.op x x) := by grind
  clear eq1712
  have eq1725 : (M.op x (M.op x y)) = (M.op x x) := by
    first
    | (have i₁ := eq182 x
       have i₂ := eq1714
       grind)
    | exact superpose eq1714 eq182
    | exact resolve eq182 eq1714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq1750 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1725
       have i₂ := eq1714
       grind)
    | exact superpose eq1714 eq1725
    | exact resolve eq1725 eq1714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1714 eq1725
  have eq1761 : x = (M.op x y) := by
    first
    | exact superpose eq1026 eq1750
    | exact resolve eq1750 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026 eq1750
  have eq1770 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq1761
       grind)
    | exact superpose eq1761 eq22
    | exact resolve eq22 eq1761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1761
  have eq1802 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1770 eq20
    | exact resolve eq20 eq1770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1770
  have eq1820 : False := by grind
  exact eq1820

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_x_pyx_y_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq44
    | exact resolve eq44 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq73 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq69 sF2
       grind)
    | exact superpose eq69 eq72
    | exact resolve eq72 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq76 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq69 sF2
       grind)
    | exact superpose eq69 eq50
    | exact resolve eq50 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq77 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq76
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq76
    | exact resolve eq76 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq76
  have eq91 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq103 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op X0 X0) X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq103 y x
       grind)
    | exact superpose eq103 eq91
    | (have j1 := eq103 y x
       grind)
    | exact resolve eq91 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq130 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq122
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq122
    | exact resolve eq122 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq132 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq130
    | exact resolve eq130 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq857 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq132 eq103
    | (have j0 := eq103 (σ y) (σ x)
       grind)
    | exact resolve eq103 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq132
  have eq858 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq857
    | exact resolve eq857 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq861 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq858
       have r₂ := eq28
       grind)
    | exact resolve eq858 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq914 : (τ (σ y)) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq861 eq77
    | exact resolve eq77 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq861
  have eq932 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq914
    | exact resolve eq914 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq914
  have eq933 : y = (M.op x x) := by grind
  clear eq932
  have eq937 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq933
       grind)
    | exact superpose eq933 eq73
    | exact resolve eq73 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq940 : x = (M.op x y) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq933
       grind)
    | exact superpose eq933 eq54
    | exact resolve eq54 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933
  have eq954 : x = (M.op x y) := by
    first
    | (have i₁ := eq940
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq940
    | exact resolve eq940 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq940
  have eq955 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq937
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq937
    | exact resolve eq937 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq937
  have eq956 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq954 eq21
    | exact resolve eq21 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq954
  have eq975 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq956
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq956
    | exact resolve eq956 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq956
  have eq1043 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq975 eq27
    | exact resolve eq27 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1113 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq975 eq955
    | exact resolve eq955 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955 eq975
  have eq1117 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1113 eq54
    | exact resolve eq54 eq1113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1113
  have eq1389 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1117 eq1043
    | exact resolve eq1043 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043 eq1117
  have eq1390 : False := by grind
  exact eq1390

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_pxy_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq13 X0 (M.op X0 X0)
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
  have eq178 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op X0 X0)
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq26 eq180
    | (have j0 := eq180 (σ y) (σ x)
       grind)
    | exact resolve eq180 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq178 (M.op X0 X0)
       have i₂ := eq180 X0 X0
       grind)
    | exact superpose eq180 eq178
    | exact resolve eq178 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq599 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq178
    | (have j1 := eq28 X0 X0
       grind)
    | exact resolve eq178 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq600 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq28 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq618 : (M.op x y) = (k y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq638 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq600 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq600 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq600 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq648 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq618
       grind)
    | exact superpose eq618 eq40
    | exact resolve eq40 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq618
  have eq649 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq648
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq648
    | exact resolve eq648 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq651 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq649
    | exact resolve eq649 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq661 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq651 eq623
    | exact resolve eq623 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq668 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq661
       have r₂ := eq27
       grind)
    | exact resolve eq661 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq676 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq668 eq194
    | exact resolve eq194 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq681 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq668 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq684 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq676
    | exact resolve eq676 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq686 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq684
       have i₂ := eq28 y y
       grind)
    | exact superpose eq28 eq684
    | (have j1 := eq28 y y
       grind)
    | exact resolve eq684 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq194 y
       have i₂ := eq684
       grind)
    | exact superpose eq684 eq194
    | exact resolve eq194 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : x = (k y y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq684
       grind)
    | exact superpose eq684 eq28
    | exact resolve eq28 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq180 y y
       have i₂ := eq684
       grind)
    | exact superpose eq684 eq180
    | exact resolve eq180 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq690
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq690
    | exact resolve eq690 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq699 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq695 eq686
    | exact resolve eq686 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq700 : (M.op x y) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq698 eq699
    | exact resolve eq699 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq701 : (M.op x y) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq698 eq700
    | exact resolve eq700 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq706 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq706 X0
       have i₂ := eq180 X0 X0
       grind)
    | exact superpose eq180 eq706
    | (have j0 := eq706 X0
       grind)
    | exact resolve eq706 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq709 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq707 X0
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq707
    | (have j0 := eq707 X0
       grind)
    | exact resolve eq707 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq707
  have eq710 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq709
    | (have j0 := eq709 X0
       have j1 := eq28 X0 X0
       grind)
    | exact resolve eq709 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq714 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq698 eq191
    | exact resolve eq191 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq716 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq698 eq27
    | exact resolve eq27 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq734 : ∀ X0 : G, x ≠ y ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq696
       grind)
    | exact superpose eq696 eq13
    | (have j0 := eq13 X0 x
       grind)
    | exact resolve eq13 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq740 : y = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq696
       grind)
    | exact superpose eq696 eq28
    | exact resolve eq28 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : ∀ X0 : G, x = (M.op (M.op X0 y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 x x x
       have i₂ := eq696
       grind)
    | exact superpose eq696 eq16
    | exact resolve eq16 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq743 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq698 eq742
    | exact resolve eq742 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq744 : y = (k (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq698 eq740
    | exact resolve eq740 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq747 : ∀ X0 : G, y ≠ (M.op x y) ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq698 eq734
    | (have j0 := eq734 X0
       grind)
    | exact resolve eq734 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq751 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq698 eq744
    | exact resolve eq744 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq752 : ∀ X0 : G, y ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq698 eq747
    | exact resolve eq747 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq874 : (σ y) = (k (M.op (σ y) (σ y)) (σ x)) ∨ (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq714 eq28
    | (have j0 := eq28 (M.op (σ y) (σ y)) (σ x)
       grind)
    | exact resolve eq28 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq877 : (σ y) = (k (M.op (σ y) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq874
       have i₂ := eq180 sF3 sF3
       grind)
    | exact superpose eq180 eq874
    | exact resolve eq874 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq874
  have eq888 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq194 y
       have i₂ := eq743 y
       grind)
    | exact superpose eq743 eq194
    | exact resolve eq194 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq927 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq888
       grind)
    | exact superpose eq888 eq28
    | exact resolve eq28 eq888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq1034 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq695
       grind)
    | exact superpose eq695 eq41
    | exact resolve eq41 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq1037 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1034
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1034
    | exact resolve eq1034 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034
  have eq1039 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1037
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1037
    | exact resolve eq1037 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037
  have eq1041 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq698 eq1039
    | exact resolve eq1039 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq1044 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq751 eq42
    | exact resolve eq42 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1047 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1044
    | exact resolve eq1044 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1049 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1047
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1047
    | exact resolve eq1047 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047
  have eq1077 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq927
       grind)
    | exact superpose eq927 eq41
    | exact resolve eq41 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq1082 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1077
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1077
    | exact resolve eq1077 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq1084 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1082
    | exact resolve eq1082 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082
  have eq1086 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1041 eq1084
    | exact resolve eq1084 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041 eq1084
  have eq1131 : y = (k y (M.op x y)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq710 y
       have i₂ := eq927
       grind)
    | exact superpose eq927 eq710
    | (have j0 := eq710 y
       grind)
    | exact resolve eq710 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq1155 : y = (k y (M.op x y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq684 eq1131
    | exact resolve eq1131 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684 eq1131
  have eq1168 : y = (k y (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq698 eq1155
    | exact resolve eq1155 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155
  have eq1169 : y = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1168
  have eq1472 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq681 eq710
    | (have j0 := eq710 (σ y)
       grind)
    | exact resolve eq710 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq1475 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq651 eq1472
    | exact resolve eq1472 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651 eq1472
  have eq1479 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq668 eq1475
    | exact resolve eq1475 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475
  have eq1480 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1479
  have eq1499 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq194 y
       have i₂ := eq1480
       grind)
    | exact superpose eq1480 eq194
    | exact resolve eq194 eq1480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1480
  have eq1505 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1499
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1499
    | exact resolve eq1499 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499
  have eq1511 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1505 eq26
    | exact resolve eq26 eq1505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1512 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1505 eq32
    | exact resolve eq32 eq1505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1505
  have eq1550 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq1512
    | exact resolve eq1512 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1512
  have eq1551 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq698 eq1511
    | exact resolve eq1511 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511
  have eq1553 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1550 eq29
    | exact resolve eq29 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1575 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32 eq1553
    | exact resolve eq1553 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553
  have eq1669 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1551 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1551
       grind)
    | exact resolve eq13 eq1551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1677 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq1669 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1669
  have eq1697 : y = (k y (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq710 y
       have i₂ := eq701
       grind)
    | exact superpose eq701 eq710
    | (have j0 := eq710 y
       grind)
    | exact resolve eq710 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701 eq710
  have eq1703 : y = (k y (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1169 eq1697
    | exact resolve eq1697 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169 eq1697
  have eq1704 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1703
  have eq3410 : (σ y) = (k (M.op (σ y) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1677 eq714
    | exact resolve eq714 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq3412 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1677 eq1551
    | exact resolve eq1551 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551 eq1677
  have eq3474 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq3412
  have eq3475 : (σ y) = (k (M.op (σ y) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq3410
  have eq3499 : (σ y) = (k (M.op (σ y) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq877 eq3475
    | exact resolve eq3475 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877 eq3475
  have eq3518 : (σ y) = (k (M.op (σ y) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3499
       have r₂ := eq716
       grind)
    | exact resolve eq3499 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716 eq3499
  have eq3535 : (τ (σ y)) = (k (τ (M.op (σ y) (σ y))) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3518 eq142
    | exact resolve eq142 eq3518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3518
  have eq3538 : y = (k (τ (M.op (σ y) (σ y))) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq3535
    | exact resolve eq3535 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3535
  have eq3544 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3474 eq142
    | exact resolve eq142 eq3474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3474
  have eq3556 : x = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30 eq3544
    | exact resolve eq3544 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3544
  have eq3560 : y = (k (τ (σ x)) x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq668 eq3538
    | exact resolve eq3538 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668 eq3538
  have eq3569 : y = (k x x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq3560
    | exact resolve eq3560 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3560
  have eq3582 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq638 x X0
       have i₂ := eq3556
       grind)
    | exact superpose eq3556 eq638
    | (have j0 := eq638 x X0
       grind)
    | (have r₁ := eq638 x x
       have r₂ := eq3556
       grind)
    | exact resolve eq638 eq3556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3586 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq3582 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3582
  have eq3874 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3586 y
       grind)
    | exact superpose eq3586 eq18
    | (have j1 := eq3586 y
       grind)
    | exact resolve eq18 eq3586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3586
  have eq3967 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1550 eq3874
    | exact resolve eq3874 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550 eq3874
  have eq3992 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq3556
       have i₂ := eq3967
       grind)
    | exact superpose eq3967 eq3556
    | exact resolve eq3556 eq3967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3556 eq3967
  have eq4002 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq3992
  have eq4008 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4002 eq29
    | exact resolve eq29 eq4002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4002
  have eq4030 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq4008
    | exact resolve eq4008 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq4008
  have eq4036 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4030
       grind)
    | exact superpose eq4030 eq18
    | exact resolve eq18 eq4030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4452 : x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq599 x
       have i₂ := eq3569
       grind)
    | exact superpose eq3569 eq599
    | (have j0 := eq599 x
       grind)
    | exact resolve eq599 eq3569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4466 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1049 eq599
    | (have j0 := eq599 (σ (M.op x y))
       grind)
    | exact resolve eq599 eq1049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599 eq1049
  have eq4497 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1086 eq4466
    | exact resolve eq4466 eq1086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4466
  have eq4504 : x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq4452
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4452
    | exact resolve eq4452 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4452
  have eq4505 : x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq4504
  have eq4509 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq4497
    | exact resolve eq4497 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4497
  have eq4510 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq4509
  have eq4516 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4030 eq4505
    | exact resolve eq4505 eq4030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4505
  have eq4519 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1086 eq4510
    | exact resolve eq4510 eq1086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086 eq4510
  have eq4582 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4519 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq4519
       grind)
    | exact resolve eq13 eq4519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4597 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4582 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4582
  have eq4831 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4597 eq4519
    | exact resolve eq4519 eq4597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4519 eq4597
  have eq4904 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4831
  have eq4963 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4904 eq142
    | exact resolve eq142 eq4904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq4904
  have eq4977 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq4963
    | exact resolve eq4963 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4963
  have eq4982 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq698 eq4977
    | exact resolve eq4977 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698 eq4977
  have eq4986 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4982 eq751
    | exact resolve eq751 eq4982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq4995 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4982 eq638
    | (have j0 := eq638 (M.op x y) X0
       grind)
    | (have r₁ := eq638 (M.op x y) x
       have r₂ := eq4982
       grind)
    | exact resolve eq638 eq4982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq4999 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4995 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4995
  have eq5003 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4986
  have eq5005 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq4999 X0
       have j1 := eq752 X0
       grind)
    | (have r₁ := eq4999 X0
       have r₂ := eq752 X0
       grind)
    | exact resolve eq4999 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752 eq4999
  have eq5009 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5003 eq27
    | exact resolve eq27 eq5003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5003
  have eq5044 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5005 eq1704
    | exact resolve eq1704 eq5005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1704 eq5005
  have eq5114 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5044
  have eq5155 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4982 eq5114
    | exact resolve eq5114 eq4982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4982 eq5114
  have eq5156 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5155
  have eq5220 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5156 eq42
    | exact resolve eq42 eq5156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq5156
  have eq5235 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq5220
    | exact resolve eq5220 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5220
  have eq6951 : x = (M.op x (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4516 eq194
    | exact resolve eq194 eq4516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4516
  have eq6979 : x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4036 eq6951
    | exact resolve eq6951 eq4036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6951
  have eq6980 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq6979
  have eq7002 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq6980
       grind)
    | exact superpose eq6980 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq6980
       grind)
    | exact resolve eq13 eq6980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7019 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq7002 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7002
  have eq7226 : x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6980
       have i₂ := eq7019 x
       grind)
    | exact superpose eq7019 eq6980
    | exact resolve eq6980 eq7019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6980 eq7019
  have eq7307 : x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq7226
  have eq7361 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3569
       have i₂ := eq7307
       grind)
    | exact superpose eq7307 eq3569
    | exact resolve eq3569 eq7307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3569 eq7307
  have eq7375 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq7361
  have eq7382 : x = y ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1575 eq7375
    | exact resolve eq7375 eq1575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1575 eq7375
  have eq7386 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4030 eq7382
    | exact resolve eq7382 eq4030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4030 eq7382
  have eq7387 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq7386
  have eq7481 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7387 eq194
    | exact resolve eq194 eq7387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq7387
  have eq7510 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4036 eq7481
    | exact resolve eq7481 eq4036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4036 eq7481
  have eq7511 : x = (M.op x y) := by grind
  clear eq7510
  have eq7514 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq7511
       grind)
    | exact superpose eq7511 eq22
    | exact resolve eq22 eq7511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq7511
  have eq7536 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq7514 eq20
    | exact resolve eq20 eq7514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq7591 : (σ x) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7536 eq5009
    | (have r₁ := eq5009
       have r₂ := eq7536
       grind)
    | exact resolve eq5009 eq7536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5009
  have eq7592 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7536 eq5235
    | exact resolve eq5235 eq7536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5235
  have eq7605 : y = (M.op x y) := by grind
  clear eq7591
  have eq7624 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq7605
       grind)
    | exact superpose eq7605 eq24
    | exact resolve eq24 eq7605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq7605
  have eq7699 : (σ x) = (σ y) := by
    first
    | exact superpose eq7514 eq7624
    | exact resolve eq7624 eq7514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7514 eq7624
  have eq7704 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq7699 eq26
    | exact resolve eq26 eq7699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq7699
  have eq7908 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7704 eq28
    | exact resolve eq28 eq7704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq7704
  have eq7918 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7592 eq7908
    | exact resolve eq7908 eq7592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7592 eq7908
  have eq7919 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7918
  have eq7930 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq7919 eq27
    | exact resolve eq27 eq7919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq7919
  have eq7938 : False := by grind
  exact eq7938

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_pyx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
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
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq74 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq86 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq67
    | (have j0 := eq67 (σ x) (σ X0)
       grind)
    | exact resolve eq67 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq91 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq67 x x
       grind)
    | exact superpose eq67 eq43
    | (have j1 := eq67 x x
       grind)
    | exact resolve eq43 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq100
    | exact resolve eq100 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq114 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq53 X0
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq114 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq103 eq67
    | (have j0 := eq67 (σ x) (σ y)
       grind)
    | exact resolve eq67 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq121
    | exact resolve eq121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq122
       have r₂ := eq27
       grind)
    | exact resolve eq122 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq127 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq27
    | exact resolve eq27 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  clear eq37
  have eq148 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq137 eq16
    | exact resolve eq16 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq222 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op X0 x) (M.op (M.op X1 (M.op x y)) (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq223 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq127 eq51
    | exact resolve eq51 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq223 eq53
    | exact resolve eq53 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op X0 (M.op (M.op (σ x) (σ x)) X1)) (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq223 eq14
    | exact resolve eq14 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq257 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (M.op (σ x) (σ x))) = (k (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq229 eq12
    | (have j0 := eq12 (M.op (σ x) (σ x)) (σ x)
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ x)) (σ x)
       have r₂ := eq229
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq229
       grind)
    | exact resolve eq12 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq259 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (M.op (σ x) (σ x))) = (k (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq257
  have eq261 : (σ x) = (k (M.op (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq259
       have i₂ := eq53 sF2
       grind)
    | exact superpose eq53 eq259
    | exact resolve eq259 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq365 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq117
    | (have r₁ := eq117
       have r₂ := eq127
       grind)
    | exact resolve eq117 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq366 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq365
  have eq369 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq366 eq103
    | exact resolve eq103 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq372 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq369
  have eq378 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq372 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq372
       grind)
    | exact resolve eq13 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq382 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq378 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq414 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq53 (σ X0)
       have i₂ := eq85 X0 X0
       grind)
    | exact superpose eq85 eq53
    | (have j1 := eq85 X0 (k X0 X0)
       grind)
    | exact resolve eq53 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq85 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq500 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 y x X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 y x X0 X1
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (σ y) X1)) (M.op X0 (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ y) (σ x) X0 X1
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X5 (M.op X4 X1)) (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op X1 X0) X1 X2 (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ x)) = (M.op (M.op X2 (M.op X0 (M.op (σ x) X1))) (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq230 X0 (M.op (M.op X2 (M.op sF2 x)) (M.op X2 (M.op sF2 x)))
       have i₂ := eq52 sF2 sF2 X2 x
       grind)
    | exact superpose eq52 eq230
    | exact resolve eq230 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq230
  have eq605 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq382 eq103
    | exact resolve eq103 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq382
  have eq609 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq605
  have eq614 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq609
    | exact resolve eq609 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq616 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq614
       have r₂ := eq27
       grind)
    | exact resolve eq614 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq627 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ (M.op x y))) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq616 eq14
    | exact resolve eq14 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq703 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq55 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55
    | (have j0 := eq55 y x
       grind)
    | exact resolve eq55 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq13
    | (have j0 := eq13 X0 X0
       grind)
    | exact resolve eq13 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq732 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X2
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1460 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) X0) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq539 (M.op sF2 x) x (M.op sF2 x)
       have i₂ := eq53 (M.op sF2 x)
       grind)
    | exact superpose eq53 eq539
    | exact resolve eq539 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq1880 : ∀ X0 : G, (σ x) ≠ (σ (k x X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq86 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq2609 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq222 X0 sF0
       have i₂ := eq55 sF0 sF0
       grind)
    | exact superpose eq55 eq222
    | exact resolve eq222 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq3420 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq418 x y
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq418
    | (have j0 := eq418 x y
       grind)
    | exact resolve eq418 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq418
  have eq3443 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3420
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3420
    | exact resolve eq3420 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3420
  have eq3467 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq3443
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3443
    | exact resolve eq3443 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3443
  have eq3488 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq3467
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3467
    | exact resolve eq3467 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3467
  have eq3497 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3488
    | exact resolve eq3488 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3488
  have eq3679 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq508
    | (have j0 := eq508 (σ y) X0 (σ x)
       grind)
    | exact resolve eq508 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3774 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq508 X0 X0 X1
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq508
    | exact resolve eq508 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq5466 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq414 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq414
    | (have j0 := eq414 (τ X0)
       grind)
    | exact resolve eq414 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq414
  have eq5487 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5466 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5466
    | (have j0 := eq5466 X0
       grind)
    | exact resolve eq5466 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5466
  have eq5496 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5487 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5487
    | (have j0 := eq5487 X0
       grind)
    | exact resolve eq5487 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5487
  have eq5774 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq500 (M.op y X0) X0
       have i₂ := eq55 (M.op y X0) (M.op y X0)
       grind)
    | exact superpose eq55 eq500
    | exact resolve eq500 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq5802 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq627 eq502
    | exact resolve eq502 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502 eq627
  have eq5825 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq5802
    | exact resolve eq5802 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5802
  have eq5847 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq5825
  have eq5854 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5847 eq1460
    | exact resolve eq1460 eq5847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460
  have eq5862 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5847 eq14
    | exact resolve eq14 eq5847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5847
  have eq5872 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq5854
  have eq5882 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5872 eq616
    | exact resolve eq616 eq5872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5872
  have eq5930 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq5882
  have eq6249 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq510 X0 X0 X2 X3 X1
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq510
    | exact resolve eq510 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq6282 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5930 eq51
    | exact resolve eq51 eq5930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq6286 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5930 eq261
    | exact resolve eq261 eq5930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq6365 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq6286
  have eq6371 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq6365
       have r₂ := eq129
       grind)
    | exact resolve eq6365 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6365
  have eq6547 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq118 X0
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq118
    | (have j0 := eq118 X0
       grind)
    | exact resolve eq118 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq6579 : (τ (σ x)) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6371 eq148
    | exact resolve eq148 eq6371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq6371
  have eq6582 : x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq6579
    | exact resolve eq6579 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq6579
  have eq6714 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq6582
       have i₂ := eq67 sF0 x
       grind)
    | exact superpose eq67 eq6582
    | (have j1 := eq67 (M.op x y) x
       grind)
    | exact resolve eq6582 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6582
  have eq9026 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq509 (M.op X1 X2) X1 X2 (M.op X1 X2) x x
       have i₂ := eq53 (M.op X1 X2)
       grind)
    | exact superpose eq53 eq509
    | exact resolve eq509 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq18574 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq6714 eq3774
    | exact resolve eq3774 eq6714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3774
  have eq20112 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq6714 eq18574
    | exact resolve eq18574 eq6714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6714 eq18574
  have eq20136 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by grind
  clear eq20112
  have eq20147 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq20136
       grind)
    | exact superpose eq20136 eq53
    | exact resolve eq53 eq20136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20136
  have eq39524 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (σ x)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5862 eq732
    | exact resolve eq732 eq5862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732 eq5862
  have eq40805 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq616 eq39524
    | exact resolve eq39524 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616 eq39524
  have eq40871 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq40805
  have eq40955 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op (σ (M.op x y)) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq40871 eq55
    | exact resolve eq55 eq40871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq40871
  have eq44613 : (M.op (σ (M.op x y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40955 eq3679
    | exact resolve eq3679 eq40955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3679
  have eq44658 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq44613
    | exact resolve eq44613 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44613
  have eq44719 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq44658
  have eq44721 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq44719
    | exact resolve eq44719 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44719
  have eq44744 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq44721 eq40955
    | exact resolve eq40955 eq44721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40955 eq44721
  have eq44763 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq44744
  have eq44785 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq44763
    | exact resolve eq44763 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq44816 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq44763 eq6282
    | exact resolve eq6282 eq44763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6282 eq44763
  have eq44859 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq44816
  have eq44885 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq44785
  have eq45575 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq44885 eq5930
    | exact resolve eq5930 eq44885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5930 eq44885
  have eq45691 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq45575
  have eq45718 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45691 eq29
    | exact resolve eq29 eq45691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq45921 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq45718
    | exact resolve eq45718 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq45718
  have eq46033 : x = (M.op y x) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45921 eq20147
    | exact resolve eq20147 eq45921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20147
  have eq46069 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq46070 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46033
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq46033
    | exact resolve eq46033 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46033
  have eq46071 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq46070
  have eq75015 : x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq46071
       have r₂ := eq46069
       grind)
    | exact resolve eq46071 eq46069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46071
  have eq75021 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2609 y
       have i₂ := eq75015
       grind)
    | exact superpose eq75015 eq2609
    | exact resolve eq2609 eq75015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2609 eq75015
  have eq75522 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq45921 eq75021
    | exact resolve eq75021 eq45921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75021
  have eq75578 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq75522
       have r₂ := eq46069
       grind)
    | exact resolve eq75522 eq46069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46069 eq75522
  have eq75579 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75578
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq75578
    | exact resolve eq75578 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75578
  have eq75588 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq53 y
       have i₂ := eq75579
       grind)
    | exact superpose eq75579 eq53
    | exact resolve eq53 eq75579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75592 : ∀ X0 : G, y ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq730 y x
       have i₂ := eq75579
       grind)
    | exact superpose eq75579 eq730
    | exact resolve eq730 eq75579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75579
  have eq75626 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq75592 X0
       grind)
    | (have r₁ := eq75592 X0
       have r₂ := eq45921
       grind)
    | exact resolve eq75592 eq45921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45921 eq75592
  have eq79775 : (k (σ y) (σ (M.op x y))) = (σ (M.op y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq75626 eq74
    | exact resolve eq74 eq75626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq75626
  have eq119203 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq75588 eq79775
    | exact resolve eq79775 eq75588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75588 eq79775
  have eq119290 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq119203
  have eq119296 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq119290
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq119290
    | exact resolve eq119290 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119290
  have eq119715 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq119296 eq67
    | (have j0 := eq67 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq67 eq119296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq119296
  have eq119725 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq119715
  have eq119782 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq119725 eq44859
    | exact resolve eq44859 eq119725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44859 eq119725
  have eq119875 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq119782
  have eq120034 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq119875 eq45691
    | exact resolve eq45691 eq119875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45691 eq119875
  have eq120135 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq120034
  have eq120234 : x = (M.op x y) := by
    first
    | (have r₁ := eq120135
       have r₂ := eq129
       grind)
    | exact resolve eq120135 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq120135
  have eq120263 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq120234 eq20
    | exact resolve eq20 eq120234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq120321 : y = (M.op x (M.op y y)) := by
    first
    | exact superpose eq120234 eq703
    | exact resolve eq703 eq120234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq120509 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq120263
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq120263
    | exact resolve eq120263 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120263
  have eq120513 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq120509 eq26
    | exact resolve eq26 eq120509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120610 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq120509 eq3497
    | exact resolve eq3497 eq120509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3497
  have eq120879 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq120610
       have r₂ := eq27
       grind)
    | exact resolve eq120610 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120610
  have eq120989 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op (M.op y X0) (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq9026 y X0 x y
       have i₂ := eq120321
       grind)
    | exact superpose eq120321 eq9026
    | exact resolve eq9026 eq120321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9026
  have eq121010 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 (M.op X1 y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq6249 x X0 X1 (M.op y y)
       have i₂ := eq120321
       grind)
    | exact superpose eq120321 eq6249
    | exact resolve eq6249 eq120321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6249 eq120321
  have eq121024 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op (M.op x y) (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq120989 X0
       have i₂ := eq5774 X0
       grind)
    | exact superpose eq5774 eq120989
    | exact resolve eq120989 eq5774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5774 eq120989
  have eq121026 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op x (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq120234 eq121024
    | exact resolve eq121024 eq120234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121024
  have eq132433 : (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq121010 y y
       have i₂ := eq53 y
       grind)
    | exact superpose eq53 eq121010
    | exact resolve eq121010 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121010
  have eq133987 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq121026 (M.op y y)
       have i₂ := eq53 y
       grind)
    | exact superpose eq53 eq121026
    | exact resolve eq121026 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq121026
  have eq134049 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq133987
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq133987
    | exact resolve eq133987 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq133987
  have eq134058 : y = (M.op y x) := by
    first
    | exact superpose eq120234 eq134049
    | exact resolve eq134049 eq120234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120234 eq134049
  have eq134063 : y = (M.op x x) := by
    first
    | (have i₁ := eq134058
       have i₂ := eq132433
       grind)
    | exact superpose eq132433 eq134058
    | exact resolve eq134058 eq132433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134058
  have eq134069 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq91
       have i₂ := eq134063
       grind)
    | exact superpose eq134063 eq91
    | exact resolve eq91 eq134063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq134093 : ∀ X0 : G, x ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq730 x x
       have i₂ := eq134063
       grind)
    | exact superpose eq134063 eq730
    | exact resolve eq730 eq134063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134096 : (k x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq6547 x
       have i₂ := eq134063
       grind)
    | exact superpose eq134063 eq6547
    | exact resolve eq6547 eq134063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6547
  have eq134129 : (k x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq134096
       have i₂ := eq132433
       grind)
    | exact superpose eq132433 eq134096
    | exact resolve eq134096 eq132433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132433 eq134096
  have eq134138 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq120509 eq134069
    | exact resolve eq134069 eq120509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134069
  have eq134140 : y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq134129
       have i₂ := eq134063
       grind)
    | exact superpose eq134063 eq134129
    | exact resolve eq134129 eq134063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134129
  have eq134142 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq134138
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq134138
    | exact resolve eq134138 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134138
  have eq134730 : (σ y) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1880 y
       have i₂ := eq134140
       grind)
    | exact superpose eq134140 eq1880
    | (have j0 := eq1880 y
       grind)
    | exact resolve eq1880 eq134140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1880 eq134140
  have eq134747 : (σ y) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq120509 eq134730
    | exact resolve eq134730 eq120509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134730
  have eq134776 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq134747
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq134747
    | exact resolve eq134747 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134747
  have eq134802 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | (have i₁ := eq134776
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq134776
    | exact resolve eq134776 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134776
  have eq134817 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq134802
    | exact resolve eq134802 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq134802
  have eq134828 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq120509 eq134817
    | exact resolve eq134817 eq120509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134817
  have eq134837 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | (have r₁ := eq134828
       have r₂ := eq27
       grind)
    | exact resolve eq134828 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134828
  have eq134874 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq134142 eq5496
    | (have j0 := eq5496 (σ (M.op x y))
       grind)
    | exact resolve eq5496 eq134142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5496
  have eq134888 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq120513 eq134874
    | exact resolve eq134874 eq120513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120513 eq134874
  have eq134893 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq134888
       have r₂ := eq27
       grind)
    | exact resolve eq134888 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq134888
  have eq136542 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq134893 eq730
    | (have r₁ := eq730 (σ (M.op x y)) x
       have r₂ := eq134893
       grind)
    | exact resolve eq730 eq134893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq136570 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq136542 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136542
  have eq144814 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq136570 eq134142
    | exact resolve eq134142 eq136570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134142 eq136570
  have eq145001 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq144814
  have eq145196 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq145001 eq134893
    | exact resolve eq134893 eq145001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134893 eq145001
  have eq145267 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq145196
  have eq145275 : x = y := by
    first
    | (have r₁ := eq145267
       have r₂ := eq134837
       grind)
    | exact resolve eq145267 eq134837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134837 eq145267
  have eq145288 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq145275
       grind)
    | exact superpose eq145275 eq24
    | exact resolve eq24 eq145275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145499 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq134093 X0
       have i₂ := eq145275
       grind)
    | exact superpose eq145275 eq134093
    | (have r₁ := eq134093 X0
       have r₂ := eq145275
       grind)
    | exact resolve eq134093 eq145275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134093 eq145275
  have eq145505 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq145499 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145499
  have eq145643 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq145288
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq145288
    | exact resolve eq145288 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq145288
  have eq145763 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq120509 eq145643
    | exact resolve eq145643 eq120509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145643
  have eq146026 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq145763 eq120879
    | exact resolve eq120879 eq145763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120879
  have eq148421 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq145505 x
       grind)
    | exact superpose eq145505 eq43
    | exact resolve eq43 eq145505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq145505
  have eq148772 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq148421
       have i₂ := eq134063
       grind)
    | exact superpose eq134063 eq148421
    | exact resolve eq148421 eq134063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134063 eq148421
  have eq148946 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq120509 eq148772
    | exact resolve eq148772 eq120509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120509 eq148772
  have eq149094 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq148946
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq148946
    | exact resolve eq148946 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq148946
  have eq149231 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq145763 eq149094
    | exact resolve eq149094 eq145763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145763 eq149094
  have eq149345 : False := by grind
  exact eq149345

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_y_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
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
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq53 X0
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : x ≠ (M.op x y) ∨ y = (M.op y y) ∨ y = (k x y) := by
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
  have eq70 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq67 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq77 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq88 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq89 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq89
    | (have j0 := eq89 (σ X0) (σ X1)
       grind)
    | exact resolve eq89 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq89 x y
       grind)
    | exact superpose eq89 eq44
    | (have j1 := eq89 x y
       grind)
    | exact resolve eq44 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq118 eq89
    | (have j0 := eq89 (σ x) (σ y)
       grind)
    | exact resolve eq89 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq123
    | exact resolve eq123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq124
       have r₂ := eq27
       grind)
    | exact resolve eq124 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq129 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq127
    | exact resolve eq127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq140 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq141 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq175 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq141 eq16
    | exact resolve eq16 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq129 eq51
    | exact resolve eq51 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 : G, (M.op X1 (σ x)) = (M.op (M.op X0 (σ x)) (M.op (M.op X1 (σ x)) (M.op X1 (σ x)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq223 eq14
    | exact resolve eq14 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq364 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129 eq70
    | (have r₁ := eq70
       have r₂ := eq129
       grind)
    | exact resolve eq70 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq365 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq364
  have eq368 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq365 eq118
    | exact resolve eq118 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq371 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq368
  have eq378 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq371 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq371
       grind)
    | exact resolve eq13 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq382 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq378 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq415 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (M.op (σ X0) X2)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) X1 X2
       have i₂ := eq97 X0 X0
       grind)
    | exact superpose eq97 eq14
    | (have j1 := eq97 X0 X0
       grind)
    | exact resolve eq14 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq97 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq487 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X0) X0 X1 X2
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (σ y) X1)) (M.op X0 (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ y) (σ x) X0 X1
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq512 : ∀ X0 X1 X2 : G, (M.op X0 (σ x)) = (M.op (M.op X2 (M.op X1 (M.op (σ x) (σ y)))) (M.op (M.op X0 (σ x)) (M.op X0 (σ x)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq52
  have eq730 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq55 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55
    | (have j0 := eq55 y x
       grind)
    | exact resolve eq55 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq754 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq13
    | (have j0 := eq13 X0 X0
       grind)
    | exact resolve eq13 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq755 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op X0 X0)
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq964 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq382 eq118
    | exact resolve eq118 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq382
  have eq968 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq964
  have eq976 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq968
    | exact resolve eq968 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq979 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq976
       have r₂ := eq27
       grind)
    | exact resolve eq976 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
  have eq982 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq979 eq26
    | exact resolve eq26 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq983 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq979 eq29
    | exact resolve eq29 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq1007 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq983
    | exact resolve eq983 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq983
  have eq1010 : ∀ X0 : G, x = (M.op (M.op X0 y) (M.op x x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1007 eq50
    | exact resolve eq50 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1017 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq2335 : x = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1010 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1010
    | (have j0 := eq1010 x
       grind)
    | exact resolve eq1010 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq2349 : x = (M.op y (M.op x x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1007 eq2335
    | exact resolve eq2335 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2335
  have eq2365 : x = (M.op y (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2349
       have r₂ := eq1017
       grind)
    | exact resolve eq2349 eq1017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017 eq2349
  have eq2374 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 (M.op x x)
       have i₂ := eq2365
       grind)
    | exact superpose eq2365 eq14
    | exact resolve eq14 eq2365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2365
  have eq3982 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq418 x y
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq418
    | (have j0 := eq418 x y
       grind)
    | exact resolve eq418 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq4021 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3982
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3982
    | exact resolve eq3982 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3982
  have eq4078 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq4021
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4021
    | exact resolve eq4021 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4021
  have eq4120 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq4078
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4078
    | exact resolve eq4078 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4078
  have eq4143 : (σ x) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq4120
    | exact resolve eq4120 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4120
  have eq4258 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq506 X0 X0 X1
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq506
    | exact resolve eq506 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq5299 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq512 sF2 X1 x
       have i₂ := eq55 sF2 sF2
       grind)
    | exact superpose eq55 eq512
    | exact resolve eq512 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq5600 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq502 (M.op sF3 x) x
       have i₂ := eq55 (M.op sF3 x) (M.op sF3 x)
       grind)
    | exact superpose eq55 eq502
    | exact resolve eq502 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq5708 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq508 X0 X2 (M.op X0 X1) X1 (M.op X0 X1)
       have i₂ := eq53 (M.op X0 X1)
       grind)
    | exact superpose eq53 eq508
    | exact resolve eq508 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq5783 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq508 X0 X0 X2 X3 X1
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq508
    | exact resolve eq508 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq5845 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq71
    | (have j0 := eq71 X0
       grind)
    | exact resolve eq71 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq5882 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5845 (M.op X0 X0)
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq5845
    | (have j0 := eq5845 X0
       grind)
    | exact resolve eq5845 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5845
  have eq5973 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op (σ (M.op x y)) X1)) (σ (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq20 eq415
    | (have j0 := eq415 (M.op x y) X0 X1
       grind)
    | exact resolve eq415 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq6040 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op (σ (M.op x y)) X1)) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq141 eq5973
    | exact resolve eq5973 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq5973
  have eq6989 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq487 X0 X1 (M.op X0 X0)
       have i₂ := eq55 X0 X0
       grind)
    | exact superpose eq55 eq487
    | exact resolve eq487 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7032 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq487 X0 (M.op (M.op X0 X0) X1) X1
       have i₂ := eq55 (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq55 eq487
    | exact resolve eq487 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq11486 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq982 eq4258
    | exact resolve eq4258 eq982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11641 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129 eq11486
    | exact resolve eq11486 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11486
  have eq11662 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq11641
  have eq11673 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11662 eq982
    | exact resolve eq982 eq11662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982
  have eq11696 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq11673
  have eq11718 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11696 eq755
    | exact resolve eq755 eq11696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq11956 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129 eq11718
    | exact resolve eq11718 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11718
  have eq11982 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq11956
  have eq12138 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11982 eq11662
    | exact resolve eq11662 eq11982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11662 eq11982
  have eq12160 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq12138
  have eq31609 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (σ x)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq232 eq5783
    | exact resolve eq5783 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq5783
  have eq49751 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11696 eq6040
    | exact resolve eq6040 eq11696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6040 eq11696
  have eq49838 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq49751 X0
       grind)
    | (have r₁ := eq49751 X0
       have r₂ := eq27
       grind)
    | exact resolve eq49751 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49751
  have eq49841 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ x)) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq129 eq49838
    | exact resolve eq49838 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq49838
  have eq49937 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ x)) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq49841 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49841
  have eq50960 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq49937 eq31609
    | exact resolve eq31609 eq49937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31609 eq49937
  have eq50988 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq50960
  have eq53939 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50988 eq55
    | exact resolve eq55 eq50988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50988
  have eq53967 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq53939 eq175
    | exact resolve eq175 eq53939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq53939
  have eq54018 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12160 eq53967
    | exact resolve eq53967 eq12160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12160 eq53967
  have eq54072 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq54018
  have eq54076 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq54072
    | exact resolve eq54072 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq54072
  have eq169711 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7032 x (M.op y y)
       have i₂ := eq2374 x
       grind)
    | exact superpose eq2374 eq7032
    | exact resolve eq7032 eq2374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2374
  have eq170087 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq169711
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq169711
    | exact resolve eq169711 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169711
  have eq170114 : ∀ X0 : G, y ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq754 y x
       have i₂ := eq170087
       grind)
    | exact superpose eq170087 eq754
    | exact resolve eq754 eq170087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170087
  have eq170159 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq170114 X0
       grind)
    | (have r₁ := eq170114 X0
       have r₂ := eq1007
       grind)
    | exact resolve eq170114 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007 eq170114
  have eq173345 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq170159 eq54076
    | exact resolve eq54076 eq170159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54076
  have eq173366 : (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq170159 eq5882
    | (have j0 := eq5882 (M.op x y)
       grind)
    | exact resolve eq5882 eq170159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5882 eq170159
  have eq173526 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq173345
  have eq173661 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq173366
       have i₂ := eq4258 sF0 sF0
       grind)
    | exact superpose eq4258 eq173366
    | exact resolve eq173366 eq4258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4258 eq173366
  have eq173662 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq173661
  have eq174606 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq173526 eq173662
    | exact resolve eq173662 eq173526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173526 eq173662
  have eq174666 : x = (M.op x y) := by grind
  clear eq174606
  have eq174690 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq174666 eq20
    | exact resolve eq20 eq174666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174694 : x ≠ x ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq174666 eq69
    | (have r₁ := eq69
       have r₂ := eq174666
       grind)
    | exact resolve eq69 eq174666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq174748 : y = (M.op x (M.op y y)) := by
    first
    | exact superpose eq174666 eq730
    | exact resolve eq730 eq174666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq174850 : y = (k x y) ∨ y = (M.op y y) := by grind
  clear eq174694
  have eq174980 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq174690
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq174690
    | exact resolve eq174690 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174690
  have eq176315 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq174980 eq26
    | exact resolve eq26 eq174980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq176396 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq174980 eq4143
    | exact resolve eq4143 eq174980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4143
  have eq176700 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq176396
       have r₂ := eq27
       grind)
    | exact resolve eq176396 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176396
  have eq176812 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq176315 eq5708
    | (have j0 := eq5708 (σ y) X0 (σ x)
       grind)
    | exact resolve eq5708 eq176315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176816 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq176315 eq6989
    | (have j0 := eq6989 (σ y) (σ x)
       grind)
    | exact resolve eq6989 eq176315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6989
  have eq177011 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq176816 eq5299
    | exact resolve eq5299 eq176816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5299 eq176816
  have eq177066 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq174980 eq177011
    | exact resolve eq177011 eq174980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177011
  have eq180927 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq176812 eq7032
    | exact resolve eq7032 eq176812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7032
  have eq181029 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq180927 eq176812
    | exact resolve eq176812 eq180927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176812 eq180927
  have eq182199 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq181029 eq5708
    | exact resolve eq5708 eq181029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5708 eq181029
  have eq190850 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq174850
       grind)
    | exact superpose eq174850 eq44
    | exact resolve eq44 eq174850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq174850
  have eq190910 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq174980 eq190850
    | exact resolve eq190850 eq174980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190850
  have eq190938 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq190910
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq190910
    | exact resolve eq190910 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190910
  have eq191069 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq190938 eq89
    | (have j0 := eq89 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq89 eq190938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190938
  have eq191082 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq176315 eq191069
    | exact resolve eq191069 eq176315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191069
  have eq191090 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq176315 eq191082
    | exact resolve eq191082 eq176315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191082
  have eq191097 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq191090
       have r₂ := eq27
       grind)
    | exact resolve eq191090 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191090
  have eq191123 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq754 y x
       have i₂ := eq191097
       grind)
    | exact superpose eq191097 eq754
    | (have r₁ := eq754 y x
       have r₂ := eq191097
       grind)
    | exact resolve eq754 eq191097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191097
  have eq191154 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq191123 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191123
  have eq192220 : (k (σ (M.op x y)) (σ y)) = (σ (M.op (M.op x y) y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq140
       have i₂ := eq191154 sF0
       grind)
    | exact superpose eq191154 eq140
    | exact resolve eq140 eq191154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq191154
  have eq192541 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq174666 eq192220
    | exact resolve eq192220 eq174666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192220
  have eq192674 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq192541
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq192541
    | exact resolve eq192541 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192541
  have eq192725 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq192674
    | exact resolve eq192674 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq192674
  have eq192750 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq192725
       have r₂ := eq176700
       grind)
    | exact resolve eq192725 eq176700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176700 eq192725
  have eq192773 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq192750 eq27
    | exact resolve eq27 eq192750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq193054 : (M.op (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq192750 eq177066
    | exact resolve eq177066 eq192750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177066
  have eq193063 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq192750 eq182199
    | exact resolve eq182199 eq192750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182199
  have eq193185 : (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq193054 eq5600
    | exact resolve eq5600 eq193054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5600 eq193054
  have eq193272 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq193185
       have i₂ := eq55 sF1 sF1
       grind)
    | exact superpose eq55 eq193185
    | exact resolve eq193185 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq193185
  have eq193276 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq192750 eq193272
    | exact resolve eq193272 eq192750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193272
  have eq193842 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq193276 eq193063
    | exact resolve eq193063 eq193276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193063 eq193276
  have eq193998 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq176315 eq193842
    | exact resolve eq193842 eq176315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176315 eq193842
  have eq194002 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq192750 eq193998
    | exact resolve eq193998 eq192750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192750 eq193998
  have eq194098 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq194002 eq754
    | (have r₁ := eq754 (σ y) x
       have r₂ := eq194002
       grind)
    | exact resolve eq754 eq194002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq194129 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq194098 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194098
  have eq194396 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq194129 eq88
    | exact resolve eq88 eq194129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq194129
  have eq194705 : (τ (σ y)) = (k y y) := by
    first
    | exact superpose eq194002 eq194396
    | exact resolve eq194396 eq194002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194002 eq194396
  have eq194768 : y = (k y y) := by
    first
    | exact superpose eq29 eq194705
    | exact resolve eq194705 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq194705
  have eq194846 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq89 y y
       have i₂ := eq194768
       grind)
    | exact superpose eq194768 eq89
    | (have j0 := eq89 y y
       grind)
    | exact resolve eq89 eq194768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq194768
  have eq194858 : y = (M.op y y) := by grind
  clear eq194846
  have eq195104 : y = (M.op x y) := by
    first
    | (have i₁ := eq174748
       have i₂ := eq194858
       grind)
    | exact superpose eq194858 eq174748
    | exact resolve eq174748 eq194858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174748 eq194858
  have eq195168 : y = (M.op x y) := by
    first
    | (have i₁ := eq195104
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq195104
    | exact resolve eq195104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq195104
  have eq195175 : x = y := by
    first
    | exact superpose eq174666 eq195168
    | exact resolve eq195168 eq174666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174666 eq195168
  have eq195181 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq195175
       grind)
    | exact superpose eq195175 eq24
    | exact resolve eq24 eq195175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq195175
  have eq195559 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq195181
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq195181
    | exact resolve eq195181 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq195181
  have eq195691 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq174980 eq195559
    | exact resolve eq195559 eq174980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174980 eq195559
  have eq195791 : False := by grind
  exact eq195791

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pyx_pxx_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq13 X0 (M.op X1 X1)
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq68 y x
       grind)
    | exact superpose eq68 eq73
    | (have j1 := eq68 y x
       grind)
    | exact resolve eq73 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq93
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq93
    | exact resolve eq93 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq671 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq101 eq68
    | (have j0 := eq68 (σ y) (σ x)
       grind)
    | exact resolve eq68 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq671
    | exact resolve eq671 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq675 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq672
       have r₂ := eq28
       grind)
    | exact resolve eq672 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq680 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  have eq681 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq675 eq54
    | exact resolve eq54 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq688 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq675 eq56
    | exact resolve eq56 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq690 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq681
    | exact resolve eq681 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq694 : (k y x) = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq695 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq690
       grind)
    | exact superpose eq690 eq54
    | exact resolve eq54 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq690
       grind)
    | exact superpose eq690 eq56
    | exact resolve eq56 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq690
  have eq704 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq695
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq695
    | exact resolve eq695 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq745 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq704 eq28
    | exact resolve eq28 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq759 : ∀ X0 : G, x ≠ y ∨ (k X0 y) = (M.op y X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq702
       grind)
    | exact superpose eq702 eq13
    | (have j0 := eq13 X0 y
       grind)
    | exact resolve eq13 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1949 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq694
       grind)
    | exact superpose eq694 eq73
    | exact resolve eq73 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq694
  have eq2530 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1949
       have i₂ := eq702
       grind)
    | exact superpose eq702 eq1949
    | exact resolve eq1949 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq1949
  have eq2555 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2530
  have eq2557 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2555
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2555
    | exact resolve eq2555 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2555
  have eq2562 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2557 eq68
    | (have j0 := eq68 (σ y) (σ x)
       grind)
    | exact resolve eq68 eq2557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2557
  have eq2563 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq2562
    | exact resolve eq2562 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2562
  have eq2564 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq2563
  have eq2584 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2564 eq54
    | exact resolve eq54 eq2564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2564
  have eq2596 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq2584
    | exact resolve eq2584 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2584
  have eq2597 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq2596
  have eq2598 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq2597 eq28
    | exact resolve eq28 eq2597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2597
  have eq2884 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq680 eq101
    | exact resolve eq101 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq2887 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq2884
  have eq2944 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2887 eq688
    | exact resolve eq688 eq2887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688 eq2887
  have eq2981 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq2944
  have eq2996 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq2981
       grind)
    | exact superpose eq2981 eq54
    | exact resolve eq54 eq2981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq2981
  have eq3015 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2996
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2996
    | exact resolve eq2996 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2996
  have eq3017 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3015
       have r₂ := eq745
       grind)
    | exact resolve eq3015 eq745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745 eq3015
  have eq3019 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3017 eq30
    | exact resolve eq30 eq3017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3017
  have eq3062 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq3019
    | exact resolve eq3019 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3019
  have eq3116 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq3062 eq21
    | exact resolve eq21 eq3062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3062
  have eq3152 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq3116
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3116
    | exact resolve eq3116 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3116
  have eq3153 : x = y := by
    first
    | (have r₁ := eq3152
       have r₂ := eq2598
       grind)
    | exact resolve eq3152 eq2598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2598 eq3152
  have eq3154 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq3153
       grind)
    | exact superpose eq3153 eq19
    | exact resolve eq19 eq3153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3155 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq3153
       grind)
    | exact superpose eq3153 eq25
    | exact resolve eq25 eq3153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq3178 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq759 X0
       have i₂ := eq3153
       grind)
    | exact superpose eq3153 eq759
    | (have r₁ := eq759 X0
       have r₂ := eq3153
       grind)
    | exact resolve eq759 eq3153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq3187 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3178 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3178
  have eq3201 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3155
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3155
    | exact resolve eq3155 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3155
  have eq3202 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3201 eq27
    | exact resolve eq27 eq3201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq3210 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3201 eq101
    | exact resolve eq101 eq3201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq3201
  have eq3251 : x = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq3210
       have i₂ := eq3153
       grind)
    | exact superpose eq3153 eq3210
    | exact resolve eq3210 eq3153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3153 eq3210
  have eq3314 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq3202 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | exact resolve eq13 eq3202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6591 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq3187 x
       grind)
    | exact superpose eq3187 eq44
    | exact resolve eq44 eq3187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq3187
  have eq6647 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6591
       have i₂ := eq3154
       grind)
    | exact superpose eq3154 eq6591
    | exact resolve eq6591 eq3154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6591
  have eq6663 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq6647
    | exact resolve eq6647 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6647
  have eq7247 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6663 eq68
    | (have j0 := eq68 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq68 eq6663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq6663
  have eq7249 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3202 eq7247
    | exact resolve eq7247 eq3202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7247
  have eq7252 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq7249
       have r₂ := eq28
       grind)
    | exact resolve eq7249 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7249
  have eq7254 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3202 eq7252
    | exact resolve eq7252 eq3202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7252
  have eq7255 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7254
  have eq7435 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq7255 eq28
    | exact resolve eq28 eq7255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8588 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3251
       have i₂ := eq3154
       grind)
    | exact superpose eq3154 eq3251
    | exact resolve eq3251 eq3154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3154 eq3251
  have eq9081 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq3314 X0
       grind)
    | (have r₁ := eq3314 X0
       have r₂ := eq7255
       grind)
    | exact resolve eq3314 eq7255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3314 eq7255
  have eq9096 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9081 eq8588
    | exact resolve eq8588 eq9081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8588 eq9081
  have eq9157 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3202 eq9096
    | exact resolve eq9096 eq3202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3202 eq9096
  have eq9179 : x = (M.op x y) := by
    first
    | (have r₁ := eq9157
       have r₂ := eq28
       grind)
    | exact resolve eq9157 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq9157
  have eq9284 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq9179 eq21
    | exact resolve eq21 eq9179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq9179
  have eq9341 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq9284
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq9284
    | exact resolve eq9284 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq9284
  have eq9351 : False := by grind
  exact eq9351

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_pyx_pxy_Equation1904 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
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
  have eq25 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq31 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ (M.op X0 X0))) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq25 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq25
    | exact resolve eq25 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq25
  have eq73 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq28
    | (have j0 := eq28 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq443 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 X0 X1
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq65
    | exact resolve eq65 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq1235 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq73 x y
       grind)
    | exact superpose eq73 eq16
    | (have j1 := eq73 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq73 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq73 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq73 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1264 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1235
  have eq1706 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq443 (σ y) (σ x)
       have i₂ := eq1264
       grind)
    | exact superpose eq1264 eq443
    | exact resolve eq443 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1710 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1706
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq1706
    | exact resolve eq1706 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1706
  have eq3261 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1264
       have i₂ := eq1710
       grind)
    | exact superpose eq1710 eq1264
    | exact resolve eq1264 eq1710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264 eq1710
  have eq3303 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3261
  have eq5812 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq3303
       grind)
    | exact superpose eq3303 eq10
    | exact resolve eq10 eq3303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3303
  have eq5861 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5812
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5812
    | exact resolve eq5812 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5812
  have eq8693 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq443 y y
       have i₂ := eq5861
       grind)
    | exact superpose eq5861 eq443
    | exact resolve eq443 eq5861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5861
  have eq8701 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8693
  have eq12449 : y = (M.op x (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq31 y x
       have i₂ := eq8701
       grind)
    | exact superpose eq8701 eq31
    | exact resolve eq31 eq8701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq12465 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq443 y x
       have i₂ := eq8701
       grind)
    | exact superpose eq8701 eq443
    | exact resolve eq443 eq8701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20374 : y = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12449
       have i₂ := eq12465
       grind)
    | exact superpose eq12465 eq12449
    | exact resolve eq12449 eq12465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12449
  have eq20453 : y = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20374
  have eq59431 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq20453
       have i₂ := eq8701
       grind)
    | exact superpose eq8701 eq20453
    | exact resolve eq20453 eq8701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8701 eq20453
  have eq59520 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq59431
  have eq69645 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq56 x x
       have i₂ := eq59520
       grind)
    | exact superpose eq59520 eq56
    | exact resolve eq56 eq59520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq69646 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq57 x
       have i₂ := eq59520
       grind)
    | exact superpose eq59520 eq57
    | exact resolve eq57 eq59520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq59520
  have eq69810 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq69645 x
       have i₂ := eq443 (σ y) x
       grind)
    | exact superpose eq443 eq69645
    | exact resolve eq69645 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443 eq69645
  have eq69847 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq69810
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq69810
    | exact resolve eq69810 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69810
  have eq181615 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq69847
       have i₂ := eq12465
       grind)
    | exact superpose eq12465 eq69847
    | exact resolve eq69847 eq12465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12465 eq69847
  have eq181958 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq181615
  have eq299070 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq69646
       grind)
    | exact superpose eq69646 eq16
    | exact resolve eq16 eq69646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69646
  have eq299299 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq299070
       have r₂ := eq181958
       grind)
    | exact resolve eq299070 eq181958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181958 eq299070
  have eq317701 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq299299
       grind)
    | exact superpose eq299299 eq10
    | exact resolve eq10 eq299299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299299
  have eq318154 : x = y ∨ x = y := by
    first
    | (have i₁ := eq317701
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq317701
    | exact resolve eq317701 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317701
  have eq318155 : x = y := by grind
  clear eq318154
  have eq341219 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq318155
       grind)
    | exact superpose eq318155 eq16
    | exact resolve eq16 eq318155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318155
  have eq341220 : False := by grind
  exact eq341220
