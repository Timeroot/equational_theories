import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1043`: `x = x ◇ ((y ◇ (x ◇ z)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pyx_pyy_pxy_Equation1043 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1043 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1043.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X0 := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) X3))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 X1 (M.op (M.op X2 (M.op X0 X3)) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
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
  have eq73 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq74 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq36
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
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq85 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq78
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq87
    | exact resolve eq87 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq95 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
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
  have eq100 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq95
  have eq124 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq141 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq124
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq124
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq124 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq124 eq16
    | exact resolve eq16 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq141
  have eq269 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k y (τ X0))
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq16
    | exact resolve eq16 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq350 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) (M.op X0 (M.op (M.op X3 (M.op X0 X4)) X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X1 X0) X2 X0 (M.op (M.op X3 (M.op X0 X4)) X4)
       have i₂ := eq52 X0 X1 X3 X4
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X2 (M.op X0 X3)) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X0 (M.op (M.op X2 (M.op X0 X3)) X3)
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq351 X0 X1 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq351
    | exact resolve eq351 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq354 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X1 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq350 X0 X1 X2 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq350
    | exact resolve eq350 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq477 : (k y (k (M.op x y) (M.op x y))) = (τ (k (σ y) (k (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | exact superpose eq147 eq269
    | exact resolve eq269 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq2995 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 X0 x X0
       have i₂ := eq354 X0 X0 x
       grind)
    | exact superpose eq354 eq52
    | exact resolve eq52 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq3017 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq354 X0 X0 X0
       have i₂ := eq2995 X0
       grind)
    | exact superpose eq2995 eq354
    | exact resolve eq354 eq2995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq2995
  have eq3061 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq3017 X0
       grind)
    | exact superpose eq3017 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq3017 X0
       grind)
    | exact resolve eq13 eq3017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3066 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 (M.op X0 X0)
       have i₂ := eq3017 X0
       grind)
    | exact superpose eq3017 eq14
    | exact resolve eq14 eq3017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3067 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq3061 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3061
  have eq3070 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3066 X0 X1
       have i₂ := eq353 (M.op X0 X0) X1
       grind)
    | exact superpose eq353 eq3066
    | exact resolve eq3066 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353 eq3066
  have eq3485 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq73 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq73
    | (have j0 := eq73 x
       grind)
    | exact resolve eq73 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq3497 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3485
  have eq3500 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3497
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq3497
    | exact resolve eq3497 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3497
  have eq3516 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq3500
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq3500 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3500
  have eq3522 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3516 eq49
    | exact resolve eq49 eq3516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq3671 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq74 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq74
    | (have j0 := eq74 y
       grind)
    | exact resolve eq74 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq3683 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3671
  have eq3685 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3683
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq3683
    | exact resolve eq3683 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3683
  have eq3708 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq3685
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq3685 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3685
  have eq3736 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq3708 eq100
    | exact resolve eq100 eq3708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq3947 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq125
    | (have j0 := eq125 (M.op x y)
       grind)
    | exact resolve eq125 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq3957 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq3947
  have eq3958 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq124 eq3957
    | exact resolve eq3957 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq3957
  have eq3988 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq3958
       have r₂ := eq13 x (σ (M.op x y))
       grind)
    | exact resolve eq3958 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3958
  have eq4038 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq3988 eq147
    | exact resolve eq147 eq3988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq4797 : (k y (k (M.op x y) (M.op x y))) = (τ (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | exact superpose eq3988 eq477
    | exact resolve eq477 eq3988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq4798 : (k y (k (M.op x y) (M.op x y))) = (τ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y))) := by
    first
    | (have i₁ := eq4797
       have i₂ := eq3067 sF1 sF3
       grind)
    | exact superpose eq3067 eq4797
    | exact resolve eq4797 eq3067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4797
  have eq11132 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3516 eq85
    | exact resolve eq85 eq3516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq11763 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3708 eq101
    | exact resolve eq101 eq3708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq12775 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3988 eq148
    | exact resolve eq148 eq3988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq3988
  have eq14845 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq11132
       grind)
    | exact superpose eq11132 eq16
    | exact resolve eq16 eq11132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11132
  have eq14915 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3522 eq14845
    | exact resolve eq14845 eq3522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14845
  have eq14935 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq14915
       have r₂ := eq13 x x
       grind)
    | exact resolve eq14915 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14915
  have eq14943 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq14935
       grind)
    | exact superpose eq14935 eq43
    | exact resolve eq43 eq14935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq14980 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq3516 eq14943
    | exact resolve eq14943 eq3516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3516 eq14943
  have eq15468 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq11763
       grind)
    | exact superpose eq11763 eq16
    | exact resolve eq16 eq11763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11763
  have eq15542 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq3736 eq15468
    | exact resolve eq15468 eq3736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15468
  have eq15564 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq15542
       have r₂ := eq13 x y
       grind)
    | exact resolve eq15542 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15542
  have eq15573 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq15564
       grind)
    | exact superpose eq15564 eq70
    | exact resolve eq70 eq15564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq15605 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq3708 eq15573
    | exact resolve eq15573 eq3708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3708 eq15573
  have eq16136 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq12775 eq16
    | exact resolve eq16 eq12775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12775
  have eq16214 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4038 eq16136
    | exact resolve eq16136 eq4038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4038 eq16136
  have eq16238 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq16214
       have r₂ := eq13 x (M.op x y)
       grind)
    | exact resolve eq16214 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16214
  have eq19735 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq3070 X0 X1
       grind)
    | exact superpose eq3070 eq14
    | exact resolve eq14 eq3070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19778 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19735 X0 X1
       have i₂ := eq3017 X0
       grind)
    | exact superpose eq3017 eq19735
    | exact resolve eq19735 eq3017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3017 eq19735
  have eq19789 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3070 X1 X0
       have i₂ := eq19778 X1 X0
       grind)
    | exact superpose eq19778 eq3070
    | exact resolve eq3070 eq19778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3070
  have eq23442 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq88 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq23443 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq23442
    | exact resolve eq23442 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23442
  have eq23454 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq23443
       have r₂ := eq27
       grind)
    | exact resolve eq23443 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23443
  have eq23462 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq23454 eq3736
    | exact resolve eq3736 eq23454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3736 eq23454
  have eq23525 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq23462
       have i₂ := eq15564
       grind)
    | exact superpose eq15564 eq23462
    | exact resolve eq23462 eq15564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15564 eq23462
  have eq23536 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq23525
    | exact resolve eq23525 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq23525
  have eq23537 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq23536
  have eq23543 : (τ (σ x)) = (k x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq23537 eq3522
    | exact resolve eq3522 eq23537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3522 eq23537
  have eq23604 : (τ (σ x)) = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq23543
       have i₂ := eq14935
       grind)
    | exact superpose eq14935 eq23543
    | exact resolve eq23543 eq14935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14935 eq23543
  have eq23614 : x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq23604
    | exact resolve eq23604 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq23604
  have eq23615 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq23614
  have eq23629 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15605
       have i₂ := eq23615
       grind)
    | exact superpose eq23615 eq15605
    | exact resolve eq15605 eq23615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15605
  have eq23647 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq19778 y X0
       have i₂ := eq23615
       grind)
    | exact superpose eq23615 eq19778
    | exact resolve eq19778 eq23615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23615
  have eq23686 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq23629
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23629
    | exact resolve eq23629 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq23629
  have eq23716 : ∀ X0 X1 : G, (M.op X1 y) = X1 ∨ (M.op X0 x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19778 x X0
       have i₂ := eq23647 X1
       grind)
    | exact superpose eq23647 eq19778
    | (have j1 := eq23647 X1
       grind)
    | exact resolve eq19778 eq23647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23647
  have eq23792 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq23686 eq19778
    | exact resolve eq19778 eq23686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23686
  have eq23968 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23716 X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23716
    | (have j0 := eq23716 X0 x
       grind)
    | exact resolve eq23716 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23716
  have eq24078 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq19789 X0 x
       have i₂ := eq23968 x
       grind)
    | exact superpose eq23968 eq19789
    | exact resolve eq19789 eq23968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23968
  have eq24157 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq24078 y
       grind)
    | exact superpose eq24078 eq18
    | (have j1 := eq24078 y
       grind)
    | exact resolve eq18 eq24078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq24078
  have eq24239 : x = (M.op x y) := by grind
  clear eq24157
  have eq24264 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq24239 eq20
    | exact resolve eq20 eq24239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq24433 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq24264
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24264
    | exact resolve eq24264 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24264
  have eq25104 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq24433 eq26
    | exact resolve eq26 eq24433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28578 : ∀ X0 X1 : G, (M.op X1 (σ y)) = X1 ∨ (M.op X0 x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19778 x X0
       have i₂ := eq23792 X1
       grind)
    | exact superpose eq23792 eq19778
    | (have j1 := eq23792 X1
       grind)
    | exact resolve eq19778 eq23792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19778 eq23792
  have eq29576 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq28578 (M.op sF2 sF3) x
       grind)
    | exact superpose eq28578 eq26
    | (have j1 := eq28578 X0 (σ x)
       grind)
    | exact resolve eq26 eq28578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq28578
  have eq29605 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq24433 eq29576
    | (have j0 := eq29576 X0
       grind)
    | exact resolve eq29576 eq24433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29576
  have eq29633 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq29605 X0
       grind)
    | (have r₁ := eq29605 X0
       have r₂ := eq27
       grind)
    | exact resolve eq29605 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29605
  have eq29661 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq19789 X0 x
       have i₂ := eq29633 x
       grind)
    | exact superpose eq29633 eq19789
    | exact resolve eq19789 eq29633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29711 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14980
       have i₂ := eq29633 x
       grind)
    | exact superpose eq29633 eq14980
    | exact resolve eq14980 eq29633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14980 eq29633
  have eq29734 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq24433 eq29711
    | exact resolve eq29711 eq24433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29711
  have eq29784 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq29734
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29734
    | exact resolve eq29734 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29734
  have eq29800 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq24433 eq29784
    | exact resolve eq29784 eq24433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29784
  have eq30043 : (k y (k (M.op x y) (M.op x y))) = (τ (M.op (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq29800 eq4798
    | exact resolve eq4798 eq29800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4798 eq29800
  have eq30096 : (τ (M.op (σ x) (σ y))) = (k y (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq25104 eq30043
    | exact resolve eq30043 eq25104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25104 eq30043
  have eq30105 : (τ (M.op (σ x) (σ y))) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq16238 eq30096
    | exact resolve eq30096 eq16238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16238 eq30096
  have eq30113 : (τ (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq30105
       have i₂ := eq3067 sF0 y
       grind)
    | exact superpose eq3067 eq30105
    | exact resolve eq30105 eq3067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3067 eq30105
  have eq30121 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq30113
       have i₂ := eq19789 y sF0
       grind)
    | exact superpose eq19789 eq30113
    | exact resolve eq30113 eq19789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19789 eq30113
  have eq30126 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq24239 eq30121
    | exact resolve eq30121 eq24239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24239 eq30121
  have eq30128 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq30126
       have i₂ := eq29661 x
       grind)
    | exact superpose eq29661 eq30126
    | exact resolve eq30126 eq29661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29661 eq30126
  have eq30129 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30128 eq15
    | exact resolve eq15 eq30128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30128
  have eq30217 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30129
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30129
    | exact resolve eq30129 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq30129
  have eq30236 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24433 eq30217
    | exact resolve eq30217 eq24433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24433 eq30217
  have eq30252 : False := by grind
  exact eq30252

/-- `Equation1910`: `x = (y ◇ (x ◇ z)) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pxx_y_pyx_Equation1910 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1910 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1910.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 X2)) = X0 := by
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
  have eq85 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  clear eq47
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
  have eq174 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op X0 y)) := by
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
  have eq175 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op X1 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X2 (M.op X0 X3)) X1 (M.op X2 X3)
       have i₂ := eq16 X0 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 (M.op X1 (M.op X0 X2)) X2
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op (M.op x (M.op X0 y)) (M.op x y)) = X0 := by
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
  have eq179 : ∀ X0 : G, (M.op (M.op (σ x) (M.op X0 (σ y))) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X0 X2)) (M.op X3 (M.op X1 X2))) X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op X1 (M.op X0 X2)) (M.op X1 X2)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : x ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
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
  have eq182 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) ≠ X0 ∨ (k (M.op X1 X2) (M.op X1 (M.op X0 X2))) = (M.op (M.op X1 X2) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 X2) (M.op X1 (M.op X0 X2))
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 (M.op X1 X2) (M.op X1 (M.op X0 X2))
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : x = (M.op (M.op x (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq174 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq174
    | (have j0 := eq174 x
       grind)
    | exact resolve eq174 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op x y)) (M.op X1 (M.op X0 y))) x) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq175
    | (have j0 := eq175 (σ x)
       grind)
    | exact resolve eq175 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 : G, (M.op (σ x) (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X1 (M.op X0 (σ y)))) (σ x)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ x)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq195 eq16
    | exact resolve eq16 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 : G, (M.op (M.op (M.op x (M.op X0 y)) (M.op X1 (M.op x y))) X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 : G, (M.op x (M.op X0 y)) = (M.op (M.op X1 X0) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (σ y))) = (M.op (M.op X1 X0) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq435 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq351 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq351
    | exact resolve eq351 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq581 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op (M.op X1 x) (M.op X0 y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq177
    | exact resolve eq177 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq586 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op X0 (σ y))) (M.op (M.op X1 X0) (M.op (σ x) (σ y)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq179 eq177
    | exact resolve eq177 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k y x) := by
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
  have eq674 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq692 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq773 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq696 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq696 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq696 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | (have r₁ := eq696 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq696 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq798 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq690
       grind)
    | exact superpose eq690 eq39
    | exact resolve eq39 eq690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq799 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq798
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq798
    | exact resolve eq798 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq801 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq799
    | exact resolve eq799 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq809 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq801 eq692
    | exact resolve eq692 eq801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq816 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq809
       have r₂ := eq27
       grind)
    | exact resolve eq809 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq829 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq816 eq674
    | (have r₁ := eq674
       have r₂ := eq816
       grind)
    | exact resolve eq674 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq830 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq816
  have eq831 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq829
  have eq832 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq831
       have r₂ := eq830
       grind)
    | exact resolve eq831 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830 eq831
  have eq848 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq832 eq107
    | exact resolve eq107 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq832
  have eq855 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq848
    | exact resolve eq848 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq858 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq855
       have r₂ := eq672
       grind)
    | exact resolve eq855 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq862 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq690
       have i₂ := eq858
       grind)
    | exact superpose eq858 eq690
    | exact resolve eq690 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq863 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq858
       grind)
    | exact superpose eq858 eq36
    | exact resolve eq36 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq858
  have eq865 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq862
  have eq868 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq863
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq863
    | exact resolve eq863 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq872 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op X0 (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq865 eq175
    | exact resolve eq175 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq873 : ∀ X0 : G, (M.op (M.op (σ x) (M.op X0 (σ y))) (σ x)) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq865 eq179
    | exact resolve eq179 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq874 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq865 eq182
    | (have r₁ := eq182
       have r₂ := eq865
       grind)
    | exact resolve eq182 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq880 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq874
  have eq882 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq801 eq880
    | exact resolve eq880 eq801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801 eq880
  have eq886 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq868 eq692
    | exact resolve eq692 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq890 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq886
  have eq899 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq890 eq27
    | exact resolve eq27 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq903 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq890 eq195
    | exact resolve eq195 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq916 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq903
    | exact resolve eq903 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq921 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq890 eq916
    | exact resolve eq916 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq923 : (σ y) = (M.op (M.op (σ x) (σ (M.op x y))) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq882 eq179
    | exact resolve eq179 eq882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq935 : (σ y) = (M.op (M.op (σ x) (σ (M.op x y))) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq865 eq923
    | exact resolve eq923 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq1088 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ y) (σ x) X0 X1
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1113 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op X1 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)))) = (M.op (M.op X2 X1) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq196 eq176
    | exact resolve eq176 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1117 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X2)) = (M.op (M.op X1 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq176 X3 X1 (M.op X0 (M.op X1 X2)) X2
       have i₂ := eq177 X1 X0 X2
       grind)
    | exact superpose eq177 eq176
    | exact resolve eq176 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1224 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X1 X0 X2 X0
       have i₂ := eq176 (M.op X1 X2) X0 X0 X2
       grind)
    | exact superpose eq176 eq180
    | exact resolve eq180 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1228 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 (M.op X1 (M.op (M.op X1 X2) X2)) (M.op X1 X2)
       have i₂ := eq180 (M.op X1 X2) X1 X2 X0
       grind)
    | exact superpose eq180 eq177
    | exact resolve eq177 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1354 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (σ x) (σ (M.op x y))) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq935 eq204
    | exact resolve eq204 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1366 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (M.op (σ x) (σ (M.op x y))) (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq865 eq1354
    | exact resolve eq1354 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354
  have eq1369 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq935 eq1366
    | exact resolve eq1366 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935 eq1366
  have eq1371 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq882 eq1369
    | exact resolve eq1369 eq882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882 eq1369
  have eq1377 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1371 eq204
    | exact resolve eq204 eq1371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1395 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq865 eq1377
    | exact resolve eq1377 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377
  have eq1398 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1371 eq1395
    | exact resolve eq1395 eq1371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395
  have eq1437 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1398 eq13
    | (have r₁ := eq13 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq1398
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1398
       grind)
    | exact resolve eq13 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398
  have eq1445 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1437
  have eq1470 : (τ (σ (M.op x y))) = (k (τ (σ (M.op x y))) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1445 eq163
    | exact resolve eq163 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq1445
  have eq1473 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq1470
    | exact resolve eq1470 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470
  have eq1662 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op (σ x) (M.op X0 (σ y))) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq873 eq204
    | exact resolve eq204 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq1684 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq179 eq1662
    | exact resolve eq1662 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1662
  have eq1692 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq865 eq1684
    | exact resolve eq1684 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1684
  have eq1695 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1371 eq1692
    | exact resolve eq1692 eq1371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1692
  have eq1701 : ∀ X0 : G, (σ (M.op x y)) = (k X0 X0) ∨ (σ (M.op x y)) = X0 ∨ (σ (M.op x y)) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq1695 X0
       grind)
    | exact superpose eq1695 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1703 : ∀ X0 : G, (σ (M.op x y)) ≠ X0 ∨ (σ (M.op x y)) = (k X0 X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq1695 X0
       grind)
    | exact superpose eq1695 eq13
    | (have r₁ := eq13 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq1695 (σ (M.op x y))
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1695 X0
       grind)
    | exact resolve eq13 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1738 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq180 X0 X0 x X0
       have i₂ := eq1695 (M.op X0 (M.op X0 x))
       grind)
    | exact superpose eq1695 eq180
    | exact resolve eq180 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695
  have eq1752 : ∀ X0 : G, (σ (M.op x y)) = (k X0 X0) ∨ (σ (M.op x y)) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1701 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1701
  have eq1771 : ∀ X0 : G, (σ (M.op x y)) = (k X0 X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1752 X0
       have j1 := eq1703 X0
       grind)
    | (have r₁ := eq1752 X0
       have r₂ := eq1703 (k X0 X0)
       grind)
    | (have r₁ := eq1752 X0
       have r₂ := eq1703 X0
       grind)
    | (have r₁ := eq1752 (σ (M.op x y))
       have r₂ := eq1703 (σ (M.op x y))
       grind)
    | exact resolve eq1752 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1703 eq1752
  have eq1808 : x = (M.op (M.op x y) (M.op (σ (M.op x y)) y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1738 eq174
    | exact resolve eq174 eq1738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1834 : x = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1738 eq1808
    | exact resolve eq1808 eq1738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1808
  have eq1890 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1473
       have i₂ := eq1771 sF0
       grind)
    | exact superpose eq1771 eq1473
    | exact resolve eq1473 eq1771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1906 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1890
  have eq2002 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1906 eq1738
    | exact resolve eq1738 eq1906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1738
  have eq2003 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2002 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2002
  have eq2208 : x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2003 eq1834
    | exact resolve eq1834 eq2003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1834 eq2003
  have eq2249 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2208
  have eq2408 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2249
       grind)
    | exact superpose eq2249 eq24
    | exact resolve eq24 eq2249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2414 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq672
       have i₂ := eq2249
       grind)
    | exact superpose eq2249 eq672
    | (have r₁ := eq672
       have r₂ := eq2249
       grind)
    | exact resolve eq672 eq2249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq2418 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) x) ∨ x = y := by grind
  clear eq2414
  have eq2419 : x = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2418
  have eq2425 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2408
    | exact resolve eq2408 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2408
  have eq2440 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2425 eq899
    | (have r₁ := eq899
       have r₂ := eq2425
       grind)
    | exact resolve eq899 eq2425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq2466 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2440
  have eq2467 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2466
  have eq2472 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq865 eq2467
    | exact resolve eq2467 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2467
  have eq2473 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2472
  have eq2486 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2473 eq27
    | exact resolve eq27 eq2473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2487 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op X0 (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2473 eq175
    | exact resolve eq175 eq2473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2488 : ∀ X0 : G, (M.op (M.op (σ x) (M.op X0 (σ y))) (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2473 eq179
    | exact resolve eq179 eq2473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2489 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2473 eq182
    | (have r₁ := eq182
       have r₂ := eq2473
       grind)
    | exact resolve eq182 eq2473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq2495 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2489
  have eq2498 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2425 eq2486
    | exact resolve eq2486 eq2425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2501 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2498
  have eq2896 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2419 eq37
    | exact resolve eq37 eq2419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2419
  have eq2902 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2896
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2896
    | exact resolve eq2896 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2896
  have eq2904 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2425 eq2902
    | exact resolve eq2902 eq2425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2425 eq2902
  have eq3230 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op (σ x) (M.op X0 (σ y))) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2488 eq204
    | exact resolve eq204 eq2488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq2488
  have eq3257 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq179 eq3230
    | exact resolve eq3230 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3230
  have eq3267 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2473 eq3257
    | exact resolve eq3257 eq2473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3257
  have eq3283 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq3267 X0
       have i₂ := eq3267 sF2
       grind)
    | exact superpose eq3267 eq3267
    | exact resolve eq3267 eq3267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3291 : ∀ X0 : G, (M.op (σ x) (σ x)) = (k X0 X0) ∨ (M.op (σ x) (σ x)) = X0 ∨ (M.op (σ x) (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq3267 X0
       grind)
    | (have i₁ := eq11 (σ x) (σ x)
       have i₂ := eq3267 X0
       grind)
    | exact superpose eq3267 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq3267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3293 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ X0 ∨ (M.op (σ x) (σ x)) = (k X0 X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq3267 X0
       grind)
    | (have i₁ := eq13 (σ x) (σ x)
       have i₂ := eq3267 X0
       grind)
    | exact superpose eq3267 eq13
    | (have r₁ := eq13 (M.op (σ x) (σ x)) (M.op (σ x) (σ x))
       have r₂ := eq3267 (M.op (σ x) (σ x))
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3267 X0
       grind)
    | exact resolve eq13 eq3267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3323 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq180 X0 X0 x X0
       have i₂ := eq3267 (M.op X0 (M.op X0 x))
       grind)
    | exact superpose eq3267 eq180
    | exact resolve eq180 eq3267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3328 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2495
       have i₂ := eq3267 sF3
       grind)
    | exact superpose eq3267 eq2495
    | exact resolve eq2495 eq3267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2495
  have eq3349 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op X1 (σ x))) = (M.op (M.op X2 X1) (M.op X2 (M.op X0 X0))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X0 X1 X0 X0
       have i₂ := eq3267 X0
       grind)
    | exact superpose eq3267 eq176
    | exact resolve eq176 eq3267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3267
  have eq3366 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq3328
  have eq3375 : ∀ X0 : G, (M.op (σ x) (σ x)) = (k X0 X0) ∨ (M.op (σ x) (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3291 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3291
  have eq3383 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq3283 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3283
  have eq3396 : ∀ X0 X1 : G, (M.op (σ x) (M.op X1 (σ x))) = (M.op X0 (M.op X1 X0)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq3349 X0 X1 x
       have i₂ := eq176 X1 x X0 X0
       grind)
    | exact superpose eq176 eq3349
    | exact resolve eq3349 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3349
  have eq3404 : ∀ X0 : G, (M.op (k (σ y) (σ x)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3366 eq3323
    | exact resolve eq3323 eq3366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3323
  have eq3432 : ∀ X0 : G, (M.op (σ x) (σ x)) = (k X0 X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3375 X0
       have j1 := eq3293 X0
       grind)
    | (have r₁ := eq3375 X0
       have r₂ := eq3293 (k X0 X0)
       grind)
    | (have r₁ := eq3375 X0
       have r₂ := eq3293 X0
       grind)
    | (have r₁ := eq3375 (M.op (σ x) (σ x))
       have r₂ := eq3293 (M.op (σ x) (σ x))
       grind)
    | exact resolve eq3375 eq3293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3293 eq3375
  have eq3541 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2904 eq773
    | (have j0 := eq773 (σ y) (σ x)
       grind)
    | (have r₁ := eq773 (σ y) (σ x)
       have r₂ := eq2904
       grind)
    | exact resolve eq773 eq2904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773 eq2904
  have eq3552 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3541
  have eq3570 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq3552
    | exact resolve eq3552 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3552
  have eq3572 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq921 eq3570
    | exact resolve eq3570 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921 eq3570
  have eq3574 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq3572
       have r₂ := eq2501
       grind)
    | exact resolve eq3572 eq2501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3572
  have eq3792 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3366 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq3366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3794 : (σ x) ≠ (k (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3366 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq3366
       grind)
    | exact resolve eq13 eq3366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3803 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq3792
  have eq3822 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3803
       have r₂ := eq3794
       grind)
    | exact resolve eq3803 eq3794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3794 eq3803
  have eq3943 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq3383 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq3383 X0 X1
       grind)
    | exact superpose eq3383 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq3383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3945 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X1 X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq3383 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq3383 X0 X1
       grind)
    | exact superpose eq3383 eq13
    | (have r₁ := eq13 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq3383 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq3383 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3383 X0 X1
       grind)
    | exact resolve eq13 eq3383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3383
  have eq4026 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq3943 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3943
  have eq4139 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq4026 X0 X1
       have j1 := eq3945 X0 X1
       grind)
    | (have r₁ := eq4026 X0 X1
       have r₂ := eq3945 X0 (k X1 X1)
       grind)
    | (have r₁ := eq4026 X0 X1
       have r₂ := eq3945 X0 X1
       grind)
    | (have r₁ := eq4026 X0 (M.op X0 X0)
       have r₂ := eq3945 X0 (M.op X0 X0)
       grind)
    | exact resolve eq4026 eq3945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3945 eq4026
  have eq4430 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (k (σ y) (σ x)) X1)) X1) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq3404 eq177
    | exact resolve eq177 eq3404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4498 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq3404 eq4430
    | exact resolve eq4430 eq3404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3404 eq4430
  have eq4638 : ∀ X0 : G, (M.op (σ x) (σ x)) = (τ (k X0 X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq435 X0 X0
       have i₂ := eq3432 (τ X0)
       grind)
    | exact superpose eq3432 eq435
    | exact resolve eq435 eq3432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3432
  have eq4675 : ∀ X0 : G, (k (σ y) (σ x)) = (τ (k X0 X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3366 eq4638
    | exact resolve eq4638 eq3366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4638
  have eq4690 : ∀ X0 : G, (k (σ x) (σ x)) = (τ (k X0 X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3822 eq4675
    | exact resolve eq4675 eq3822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4675
  have eq4961 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq180 X1 X1 x X1
       have i₂ := eq4139 (M.op X1 (M.op X1 x)) X0
       grind)
    | exact superpose eq4139 eq180
    | exact resolve eq180 eq4139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4139
  have eq5349 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (M.op X0 (σ x)) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq872 (M.op X0 sF2)
       have i₂ := eq4498 X0 sF2
       grind)
    | exact superpose eq4498 eq872
    | exact resolve eq872 eq4498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5366 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (M.op X0 (σ x)) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq5349 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5349
  have eq6620 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op X0 (σ y))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3574 eq16
    | exact resolve eq16 eq3574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3574
  have eq6659 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2487 eq6620
    | exact resolve eq6620 eq2487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6620
  have eq6665 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq6659
       have r₂ := eq2501
       grind)
    | exact resolve eq6659 eq2501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2501 eq6659
  have eq6669 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq6665
       grind)
    | exact superpose eq6665 eq18
    | exact resolve eq18 eq6665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq6670 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq6665
       grind)
    | exact superpose eq6665 eq22
    | exact resolve eq22 eq6665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6674 : (M.op x y) ≠ (M.op x y) ∨ (k y (M.op x y)) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq181
       have i₂ := eq6665
       grind)
    | exact superpose eq6665 eq181
    | (have r₁ := eq181
       have r₂ := eq6665
       grind)
    | exact resolve eq181 eq6665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq6675 : (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq184
       have i₂ := eq6665
       grind)
    | exact superpose eq6665 eq184
    | exact resolve eq184 eq6665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq6680 : (k y (M.op x y)) = (M.op y y) ∨ x = y := by grind
  clear eq6674
  have eq6684 : (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4498 eq6675
    | (have j1 := eq4498 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq6675 eq4498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6675
  have eq6687 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq6670
    | exact resolve eq6670 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6670
  have eq6777 : y = (M.op (M.op x (k y (M.op x y))) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq178 y
       have i₂ := eq6680
       grind)
    | exact superpose eq6680 eq178
    | exact resolve eq178 eq6680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6778 : x = (M.op (M.op y (M.op x y)) (k y (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq174 y
       have i₂ := eq6680
       grind)
    | exact superpose eq6680 eq174
    | exact resolve eq174 eq6680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6680
  have eq6805 : (M.op x y) = (M.op (M.op y (M.op x y)) (k y (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq6665 eq6778
    | exact resolve eq6778 eq6665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6778
  have eq6806 : y = (M.op (M.op (M.op x y) (k y (M.op x y))) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq6665 eq6777
    | exact resolve eq6777 eq6665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6777
  have eq6820 : x = (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6684 eq174
    | exact resolve eq174 eq6684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6684
  have eq8131 : (k (σ x) (σ x)) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1473 eq4690
    | exact resolve eq4690 eq1473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473 eq4690
  have eq8183 : (k (σ x) (σ x)) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq8131
  have eq8223 : (k (σ x) (σ x)) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6665 eq8183
    | exact resolve eq8183 eq6665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8183
  have eq8224 : (k (σ x) (σ x)) = (τ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq8223
  have eq8247 : (σ (M.op x y)) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8224
       have i₂ := eq1771 sF2
       grind)
    | exact superpose eq1771 eq8224
    | exact resolve eq8224 eq1771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1771
  have eq8265 : ∀ X0 : G, (M.op (τ (M.op x y)) X0) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8224 eq4961
    | exact resolve eq4961 eq8224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8276 : ∀ X0 : G, (M.op (τ (M.op x y)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq8265 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8265
  have eq8291 : (σ (M.op x y)) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq8247
  have eq8303 : (σ (M.op x y)) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6665 eq8291
    | exact resolve eq8291 eq6665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8291
  have eq8304 : (σ (M.op x y)) = (τ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq8303
  have eq8421 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k (M.op (M.op X0 (σ x)) (σ y)) (σ x)) = (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op (M.op X0 (σ x)) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2487 eq183
    | (have r₁ := eq183 (σ x) (M.op (σ x) (σ x)) (σ y)
       have r₂ := eq2487 (σ x)
       grind)
    | exact resolve eq183 eq2487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8422 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k (M.op (M.op X0 (σ x)) (σ y)) (σ x)) = (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op (M.op X0 (σ x)) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq872 eq183
    | (have r₁ := eq183 (σ x) (M.op (σ x) (σ x)) (σ y)
       have r₂ := eq872 (σ x)
       grind)
    | exact resolve eq183 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq872
  have eq8450 : ∀ X0 : G, (k (M.op (M.op X0 (σ x)) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ y) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)))) ∨ (σ x) ≠ X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8422 X0
       have i₂ := eq1113 sF3 sF3 (M.op X0 sF2)
       grind)
    | exact superpose eq1113 eq8422
    | (have j0 := eq8422 X0
       grind)
    | exact resolve eq8422 eq1113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8422
  have eq8451 : ∀ X0 : G, (k (M.op (M.op X0 (σ x)) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ y) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)))) ∨ (σ x) ≠ X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8421 X0
       have i₂ := eq1113 sF3 sF3 (M.op X0 sF2)
       grind)
    | exact superpose eq1113 eq8421
    | (have j0 := eq8421 X0
       grind)
    | exact resolve eq8421 eq1113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113 eq8421
  have eq8515 : ∀ X0 : G, (k (M.op (M.op X0 (σ x)) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ y) (M.op (M.op (σ y) (σ x)) (σ y)))) ∨ (σ x) ≠ X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq865 eq8450
    | (have j0 := eq8450 X0
       grind)
    | (have r₁ := eq8450 (M.op (σ x) (σ y))
       have r₂ := eq865
       grind)
    | exact resolve eq8450 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8450
  have eq8516 : ∀ X0 : G, (k (M.op (M.op X0 (σ x)) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ y) (M.op (M.op (σ y) (σ x)) (σ y)))) ∨ (σ x) ≠ X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2473 eq8451
    | (have j0 := eq8451 X0
       grind)
    | (have r₁ := eq8451 (M.op (σ x) (σ y))
       have r₂ := eq2473
       grind)
    | exact resolve eq8451 eq2473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8451
  have eq8563 : ∀ X0 : G, (M.op (σ x) (σ x)) = (k (M.op (M.op X0 (σ x)) (σ y)) (σ x)) ∨ (σ x) ≠ X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5366 eq8515
    | (have j0 := eq8515 X0
       grind)
    | (have r₁ := eq8515 (M.op X0 (M.op (M.op X0 (σ x)) (σ y)))
       have r₂ := eq5366 X0
       grind)
    | exact resolve eq8515 eq5366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5366 eq8515
  have eq8564 : ∀ X0 : G, (k (M.op (M.op X0 (σ x)) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (M.op (M.op (σ y) (σ x)) (σ x)))) ∨ (σ x) ≠ X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3396 eq8516
    | (have j0 := eq8516 X0
       grind)
    | exact resolve eq8516 eq3396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3396 eq8516
  have eq8614 : ∀ X0 : G, (σ (M.op x y)) = (k (M.op (M.op X0 (σ x)) (σ y)) (σ x)) ∨ (σ x) ≠ X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1371 eq8563
    | (have j0 := eq8563 X0
       grind)
    | exact resolve eq8563 eq1371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371 eq8563
  have eq8615 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (M.op X0 (σ x)) (σ y)) (σ x)) ∨ (σ x) ≠ X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4498 eq8564
    | (have j0 := eq8564 X0
       grind)
    | (have r₁ := eq8564 (M.op (M.op (σ x) x) x)
       have r₂ := eq4498 (σ x) x
       grind)
    | exact resolve eq8564 eq4498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8564
  have eq8651 : ∀ X0 : G, (M.op x y) = (k (M.op (M.op X0 (σ x)) (σ y)) (σ x)) ∨ (σ x) ≠ X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1906 eq8614
    | (have j0 := eq8614 X0
       grind)
    | exact resolve eq8614 eq1906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1906 eq8614
  have eq8652 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (M.op X0 (σ x)) (σ y)) (σ x)) ∨ (σ x) ≠ X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq8615
    | (have j0 := eq8615 X0
       grind)
    | exact resolve eq8615 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq8615
  have eq8684 : ∀ X0 : G, (M.op x y) = (k (M.op (M.op X0 (σ x)) (σ y)) (σ x)) ∨ (σ x) ≠ X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6665 eq8651
    | (have j0 := eq8651 X0
       grind)
    | exact resolve eq8651 eq6665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8651
  have eq8685 : ∀ X0 : G, (M.op x y) = (k (M.op (M.op X0 (σ x)) (σ y)) (σ x)) ∨ (σ x) ≠ X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq8684 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8684
  have eq8686 : ∀ X0 : G, (M.op (σ x) (σ x)) = (k (M.op (M.op X0 (σ x)) (σ y)) (σ x)) ∨ (σ x) ≠ X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2473 eq8652
    | (have j0 := eq8652 X0
       grind)
    | (have r₁ := eq8652 (M.op (σ x) (σ y))
       have r₂ := eq2473
       grind)
    | exact resolve eq8652 eq2473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2473 eq8652
  have eq8706 : ∀ X0 : G, (k (σ y) (σ x)) = (k (M.op (M.op X0 (σ x)) (σ y)) (σ x)) ∨ (σ x) ≠ X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3366 eq8686
    | (have j0 := eq8686 X0
       grind)
    | exact resolve eq8686 eq3366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3366 eq8686
  have eq8722 : ∀ X0 : G, (k (σ x) (σ x)) = (k (M.op (M.op X0 (σ x)) (σ y)) (σ x)) ∨ (σ x) ≠ X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3822 eq8706
    | (have j0 := eq8706 X0
       grind)
    | exact resolve eq8706 eq3822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3822 eq8706
  have eq8733 : ∀ X0 : G, (τ (M.op x y)) = (k (M.op (M.op X0 (σ x)) (σ y)) (σ x)) ∨ (σ x) ≠ X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8224 eq8722
    | (have j0 := eq8722 X0
       grind)
    | exact resolve eq8722 eq8224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8224 eq8722
  have eq8740 : ∀ X0 : G, (σ (M.op x y)) = (k (M.op (M.op X0 (σ x)) (σ y)) (σ x)) ∨ (σ x) ≠ X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8304 eq8733
    | (have j0 := eq8733 X0
       grind)
    | exact resolve eq8733 eq8304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8733
  have eq8741 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8685 eq8740
    | (have j0 := eq8740 X0
       have j1 := eq8685 X0
       grind)
    | exact resolve eq8740 eq8685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8685 eq8740
  have eq8769 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq8741
  have eq8772 : (M.op x y) = (τ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8769 eq28
    | exact resolve eq28 eq8769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq8797 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8769 eq2486
    | exact resolve eq2486 eq8769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2486
  have eq8802 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  clear eq8797
  have eq8884 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8276 eq4498
    | exact resolve eq4498 eq8276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4498 eq8276
  have eq8923 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq8884 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8884
  have eq8975 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8304 eq8923
    | exact resolve eq8923 eq8304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8304 eq8923
  have eq9020 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8769 eq8975
    | exact resolve eq8975 eq8769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8769 eq8975
  have eq9337 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2487 sF3
       have i₂ := eq9020 sF3
       grind)
    | exact superpose eq9020 eq2487
    | exact resolve eq2487 eq9020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2487 eq9020
  have eq9400 : (σ x) = (M.op (M.op (σ y) (σ x)) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq9337
  have eq15926 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op (M.op X3 (M.op X0 X2)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1224 (M.op (M.op X3 (M.op X0 X2)) X1) X3 (M.op X0 X2)
       have i₂ := eq176 X1 (M.op X3 (M.op X0 X2)) X0 X2
       grind)
    | exact superpose eq176 eq1224
    | exact resolve eq1224 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15927 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X2) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1224 (M.op (M.op X1 X2) (M.op X0 X2)) X1 X2
       have i₂ := eq16 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq16 eq1224
    | exact resolve eq1224 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15960 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X0 X1 X2 (M.op X0 (M.op X1 X2))
       have i₂ := eq1224 (M.op X1 (M.op X0 X2)) X0 (M.op X1 X2)
       grind)
    | exact superpose eq1224 eq180
    | exact resolve eq180 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15961 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq177 (M.op X1 X1) X0 X1
       have i₂ := eq1224 X0 X1 X1
       grind)
    | exact superpose eq1224 eq177
    | exact resolve eq177 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15962 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) X1) X0 X1
       have i₂ := eq1224 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq1224 eq16
    | exact resolve eq16 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16003 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op x y)) = (M.op X0 (M.op (M.op y X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq178 (M.op X0 (M.op (M.op y X1) X1))
       have i₂ := eq1224 X0 y X1
       grind)
    | exact superpose eq1224 eq178
    | exact resolve eq178 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq16023 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (σ y))) = (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq196 (M.op X0 (M.op (M.op sF4 x) x))
       have i₂ := eq1224 X0 sF4 x
       grind)
    | exact superpose eq1224 eq196
    | exact resolve eq196 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq16435 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op X3 X2)) = (M.op (M.op X1 X3) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq176 X3 X1 (M.op X1 X2) X2
       have i₂ := eq1228 X0 X1 X2
       grind)
    | exact superpose eq1228 eq176
    | exact resolve eq176 eq1228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16522 : ∀ X0 X1 X3 : G, (M.op X3 X1) = (M.op (M.op X1 X3) (M.op X0 X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16435 X0 X1 x X3
       have i₂ := eq15927 X3 X1 x
       grind)
    | exact superpose eq15927 eq16435
    | exact resolve eq16435 eq15927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16435
  have eq17747 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op X0 x) (M.op (M.op (M.op x y) (M.op x y)) y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6820 eq177
    | exact resolve eq177 eq6820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6820
  have eq17780 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op X0 x) y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq17747 X0
       have i₂ := eq15961 y sF0
       grind)
    | exact superpose eq15961 eq17747
    | exact resolve eq17747 eq15961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17747
  have eq22947 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) (M.op X0 y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17780 eq177
    | exact resolve eq177 eq17780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17780
  have eq22997 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (M.op X0 x) y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22947 X0
       have i₂ := eq15960 X0 (M.op X0 x) y
       grind)
    | (have i₁ := eq22947 X0
       have i₂ := eq15960 (M.op X0 x) X0 y
       grind)
    | exact superpose eq15960 eq22947
    | exact resolve eq22947 eq15960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22947
  have eq23175 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op x (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq187 eq1224
    | exact resolve eq1224 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq23626 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq198 eq1224
    | exact resolve eq1224 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq25450 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op (M.op X1 (M.op x X2)) (M.op X0 (M.op X1 X2))) (M.op X0 y)) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22997 (M.op (M.op X1 (M.op x X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq180 x X1 X2 X0
       grind)
    | exact superpose eq180 eq22997
    | exact resolve eq22997 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq22997
  have eq25598 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op X0 (M.op (M.op (M.op X1 (M.op x X2)) (M.op X0 (M.op X1 X2))) y)) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25450 X0 X1 X2
       have i₂ := eq15960 X0 (M.op (M.op X1 (M.op x X2)) (M.op X0 (M.op X1 X2))) y
       grind)
    | (have i₁ := eq25450 X0 X1 X2
       have i₂ := eq15960 (M.op (M.op X1 (M.op x X2)) (M.op X0 (M.op X1 X2))) X0 y
       grind)
    | exact superpose eq15960 eq25450
    | exact resolve eq25450 eq15960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25450
  have eq25633 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op X0 (M.op (M.op y (M.op (M.op X1 (M.op x X2)) (M.op X1 X2))) X0)) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25598 X0 X1 X2
       have i₂ := eq15926 (M.op X1 (M.op x X2)) X0 (M.op X1 X2) y
       grind)
    | (have i₁ := eq25598 X0 X1 X2
       have i₂ := eq15926 X0 y (M.op X1 X2) (M.op X1 (M.op x X2))
       grind)
    | exact superpose eq15926 eq25598
    | exact resolve eq25598 eq15926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25598
  have eq25642 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (M.op y x) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq25633 X0 x x
       have i₂ := eq16 x x x
       grind)
    | exact superpose eq16 eq25633
    | exact resolve eq25633 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25633
  have eq27778 : ∀ X0 : G, (M.op (M.op y x) (M.op (M.op x y) X0)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq177 (M.op y x) X0 X0
       have i₂ := eq25642 X0
       grind)
    | exact superpose eq25642 eq177
    | exact resolve eq177 eq25642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25642
  have eq27864 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op y x) X0)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq27778 x
       have i₂ := eq15960 sF0 (M.op y x) x
       grind)
    | (have i₁ := eq27778 x
       have i₂ := eq15960 (M.op y x) sF0 x
       grind)
    | exact superpose eq15960 eq27778
    | exact resolve eq27778 eq15960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27778
  have eq30325 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X3 X0)) = (M.op (M.op (M.op x (M.op X1 y)) (M.op X0 (M.op x y))) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq209 eq176
    | exact resolve eq176 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30393 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op x (M.op (σ y) y)) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq209 eq179
    | exact resolve eq179 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq209
  have eq30420 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (M.op x y)) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq30393 X0
       have i₂ := eq23175 sF3
       grind)
    | exact superpose eq23175 eq30393
    | exact resolve eq30393 eq23175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30393
  have eq30486 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X3 X0)) = (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 (M.op x y))) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30325 X0 X1 X2 X3
       have i₂ := eq23175 X1
       grind)
    | (have i₁ := eq30325 X0 x X2 X3
       have i₂ := eq23175 x
       grind)
    | exact superpose eq23175 eq30325
    | exact resolve eq30325 eq23175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30325
  have eq30582 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq30420 X0
       have i₂ := eq15927 X0 sF3 sF0
       grind)
    | exact superpose eq15927 eq30420
    | exact resolve eq30420 eq15927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30420
  have eq30641 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X3 X2) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30486 X0 X1 X2 X3
       have i₂ := eq15927 X0 X1 sF0
       grind)
    | exact superpose eq15927 eq30486
    | exact resolve eq30486 eq15927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30486
  have eq30749 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op X3 (M.op (M.op X3 X2) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30641 X0 X1 X2 X3
       have i₂ := eq15960 X3 (M.op X3 X2) X0
       grind)
    | (have i₁ := eq30641 X0 X1 X2 X3
       have i₂ := eq15960 (M.op X3 X2) X3 X0
       grind)
    | exact superpose eq15960 eq30641
    | exact resolve eq30641 eq15960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30641
  have eq30812 : ∀ X0 X2 X3 : G, (M.op X2 X0) = (M.op X3 (M.op (M.op X3 X2) X0)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq30749 X0 x X2 X3
       have i₂ := eq15927 X2 X0 x
       grind)
    | exact superpose eq15927 eq30749
    | exact resolve eq30749 eq15927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30749
  have eq30940 : (M.op x (M.op (k y (M.op x y)) y)) = (M.op (M.op x y) (M.op (M.op y (M.op x y)) (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq6805 eq210
    | exact resolve eq210 eq6805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31019 : (M.op x (M.op y y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq6669 eq210
    | exact resolve eq210 eq6669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq6669
  have eq31286 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq31019
       have i₂ := eq23175 y
       grind)
    | exact superpose eq23175 eq31019
    | exact resolve eq31019 eq23175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31019
  have eq31355 : (M.op (M.op x (M.op x y)) (M.op x y)) = (M.op x (M.op (k y (M.op x y)) y)) ∨ x = y := by
    first
    | (have i₁ := eq30940
       have i₂ := eq16003 sF0 sF0
       grind)
    | exact superpose eq16003 eq30940
    | exact resolve eq30940 eq16003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16003 eq30940
  have eq31499 : (M.op (M.op x (M.op x y)) (M.op x y)) = (M.op (k y (M.op x y)) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq31355
       have i₂ := eq23175 (k y sF0)
       grind)
    | exact superpose eq23175 eq31355
    | exact resolve eq31355 eq23175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23175 eq31355
  have eq31569 : x = (M.op (k y (M.op x y)) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq31499
       have i₂ := eq15962 x sF0
       grind)
    | exact superpose eq15962 eq31499
    | exact resolve eq31499 eq15962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31499
  have eq31605 : (M.op x y) = (M.op (k y (M.op x y)) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq6665 eq31569
    | exact resolve eq31569 eq6665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31569
  have eq31654 : ∀ X0 : G, (M.op (k y (M.op x y)) (M.op (M.op X0 (M.op x y)) (M.op x y))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq31605 eq177
    | exact resolve eq177 eq31605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31605
  have eq31680 : ∀ X0 : G, (M.op (k y (M.op x y)) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq31654 X0
       have i₂ := eq15962 X0 sF0
       grind)
    | exact superpose eq15962 eq31654
    | exact resolve eq31654 eq15962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31654
  have eq31764 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (k y (M.op x y)) (M.op X0 X0)) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq31680 eq1228
    | exact resolve eq1228 eq31680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31782 : ∀ X0 X1 : G, (k y (M.op x y)) = (M.op (M.op (M.op X0 X1) X1) X0) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq31680 eq1224
    | exact resolve eq1224 eq31680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31886 : ∀ X0 : G, (M.op X0 X0) = (k y (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq31782 X0 x
       have i₂ := eq15962 X0 x
       grind)
    | exact superpose eq15962 eq31782
    | exact resolve eq31782 eq15962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31782
  have eq32411 : ∀ X0 : G, (k y (M.op x y)) = (k X0 X0) ∨ (k y (M.op x y)) = X0 ∨ (k y (M.op x y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq31886 X0
       grind)
    | exact superpose eq31886 eq11
    | exact resolve eq11 eq31886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32413 : ∀ X0 : G, (k y (M.op x y)) ≠ X0 ∨ (k y (M.op x y)) = (k X0 X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq31886 X0
       grind)
    | exact superpose eq31886 eq13
    | (have r₁ := eq13 (k y (M.op x y)) (k y (M.op x y))
       have r₂ := eq31886 (k y (M.op x y))
       grind)
    | exact resolve eq13 eq31886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31886
  have eq32557 : ∀ X0 : G, (k y (M.op x y)) = (k X0 X0) ∨ (k y (M.op x y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq32411 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32411
  have eq32629 : ∀ X0 : G, (k y (M.op x y)) = (k X0 X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq32557 X0
       have j1 := eq32413 X0
       grind)
    | (have r₁ := eq32557 X0
       have r₂ := eq32413 (k X0 X0)
       grind)
    | (have r₁ := eq32557 X0
       have r₂ := eq32413 X0
       grind)
    | (have r₁ := eq32557 (k y (M.op x y))
       have r₂ := eq32413 (k y (M.op x y))
       grind)
    | exact resolve eq32557 eq32413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32413 eq32557
  have eq32762 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = X1 ∨ x = y ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq32629 eq31680
    | exact resolve eq31680 eq32629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32764 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (k X0 X0)) (M.op x y)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq32629 eq6806
    | exact resolve eq6806 eq32629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6806
  have eq32765 : ∀ X0 : G, (M.op x y) = (M.op (M.op y (M.op x y)) (k X0 X0)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq32629 eq6805
    | exact resolve eq6805 eq32629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6805
  have eq32772 : ∀ X0 : G, (k (σ y) (σ (M.op x y))) = (σ (k X0 X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq32629 eq41
    | exact resolve eq41 eq32629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq32629
  have eq32843 : ∀ X0 : G, (M.op x y) = (M.op (M.op y (M.op x y)) (k X0 X0)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq32765 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32765
  have eq32844 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (k X0 X0)) (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq32764 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32764
  have eq32846 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = X1 ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq32762 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32762
  have eq32869 : ∀ X0 : G, (k (σ y) (σ (M.op x y))) = (σ (k X0 X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq32772 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32772
    | (have j0 := eq32772 X0
       grind)
    | exact resolve eq32772 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32772
  have eq32872 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq4961 eq32846
    | (have j0 := eq32846 X0 X1
       have j1 := eq4961 X0 X1
       grind)
    | exact resolve eq32846 eq4961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4961 eq32846
  have eq32893 : ∀ X0 : G, (k (σ y) (σ x)) = (σ (k X0 X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq6687 eq32869
    | exact resolve eq32869 eq6687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32869
  have eq37426 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op X0 (M.op y (M.op x y))) (M.op (M.op x y) (M.op x y)))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq31286 eq177
    | exact resolve eq177 eq31286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq31286
  have eq37464 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op y (M.op x y)) X0)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq37426 X0
       have i₂ := eq1117 X0 y sF0 sF0
       grind)
    | exact superpose eq1117 eq37426
    | exact resolve eq37426 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117 eq37426
  have eq38767 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) X0) = (M.op (M.op (σ x) (M.op X0 (σ y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq215 eq1224
    | exact resolve eq1224 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224
  have eq38839 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X1) = (M.op (M.op X1 (M.op (σ x) (σ y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq23626 eq38767
    | exact resolve eq38767 eq23626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38767
  have eq41452 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X2 X0)) = (M.op (M.op x y) (M.op X1 (M.op (M.op y x) X0))) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq27864 eq176
    | exact resolve eq176 eq27864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq41494 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X2 X1) X0)) = (M.op (M.op x y) (M.op X1 (M.op (M.op y x) X0))) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41452 X0 X1 X2
       have i₂ := eq15960 X2 (M.op X2 X1) X0
       grind)
    | (have i₁ := eq41452 X0 X1 X2
       have i₂ := eq15960 (M.op X2 X1) X2 X0
       grind)
    | exact superpose eq15960 eq41452
    | exact resolve eq41452 eq15960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41452
  have eq41539 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op x y) (M.op X1 (M.op (M.op y x) X0))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq41494 X0 X1 x
       have i₂ := eq30812 X0 X1 x
       grind)
    | exact superpose eq30812 eq41494
    | exact resolve eq41494 eq30812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41494
  have eq43592 : ∀ X0 : G, (M.op x y) = (M.op (M.op y (M.op x y)) (σ (k X0 X0))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq32843 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq32843
    | exact resolve eq32843 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43593 : ∀ X0 : G, (M.op x y) = (M.op (M.op y (M.op x y)) (τ (k X0 X0))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq32843 (τ X0)
       have i₂ := eq435 X0 X0
       grind)
    | exact superpose eq435 eq32843
    | exact resolve eq32843 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435 eq32843
  have eq43690 : (M.op x y) = (M.op (M.op y (M.op x y)) (k (σ y) (σ x))) ∨ x = y := by
    first
    | exact superpose eq32893 eq43592
    | exact resolve eq43592 eq32893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43592
  have eq43750 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (σ (k X0 X0))) (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq32844 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq32844
    | exact resolve eq32844 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32844
  have eq43875 : y = (M.op (M.op (M.op x y) (k (σ y) (σ x))) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq32893 eq43750
    | exact resolve eq43750 eq32893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32893 eq43750
  have eq47527 : (k (σ y) (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq43690 eq37464
    | exact resolve eq37464 eq43690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43690
  have eq47558 : (k (σ y) (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq47527
  have eq57447 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op x y) (M.op (σ y) (M.op (M.op y x) X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27864 eq1088
    | exact resolve eq1088 eq27864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27864
  have eq57550 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (σ x) (M.op X0 X1)) (σ y))) = (M.op (M.op X0 (M.op (σ y) X1)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq1088 eq215
    | exact resolve eq215 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq1088
  have eq57583 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (σ x) (M.op X0 X1)) (σ y))) = (M.op (M.op (σ y) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq57550 X0 X1
       have i₂ := eq16522 X0 (M.op sF4 sF4) (M.op X0 (M.op sF3 X1))
       grind)
    | (have i₁ := eq57550 X1 X1
       have i₂ := eq16522 sF4 X1 (M.op sF3 X1)
       grind)
    | exact superpose eq16522 eq57550
    | exact resolve eq57550 eq16522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16522 eq57550
  have eq57672 : ∀ X0 : G, (M.op (M.op x y) (M.op (σ y) (M.op (M.op y x) X0))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq57447 x
       have i₂ := eq15960 sF2 sF4 x
       grind)
    | (have i₁ := eq57447 x
       have i₂ := eq15960 sF4 sF2 x
       grind)
    | exact superpose eq15960 eq57447
    | exact resolve eq57447 eq15960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57447
  have eq57835 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op X0 X1)) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq23626 eq57583
    | exact resolve eq57583 eq23626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57583
  have eq57891 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq41539 eq57672
    | exact resolve eq57672 eq41539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41539 eq57672
  have eq58027 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op (σ y) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq30582 eq57835
    | exact resolve eq57835 eq30582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30582 eq57835
  have eq58989 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) X1) X1)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq57891 (M.op (M.op sF4 x) x)
       have i₂ := eq1228 X0 sF4 x
       grind)
    | exact superpose eq1228 eq57891
    | exact resolve eq57891 eq1228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228 eq57891
  have eq59144 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op X0 X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16023 eq58989
    | exact resolve eq58989 eq16023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16023 eq58989
  have eq59181 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23626 eq59144
    | exact resolve eq59144 eq23626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23626 eq59144
  have eq59627 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ x) (k X0 X0)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq59181 (k X0 X0)
       have i₂ := eq32872 X0 (k X0 X0)
       grind)
    | exact superpose eq32872 eq59181
    | exact resolve eq59181 eq32872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32872 eq59181
  have eq59731 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ x) (k X0 X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq59627 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59627
  have eq60647 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) (M.op X0 (k X1 X1))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq59731 eq16
    | exact resolve eq16 eq59731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59731
  have eq60724 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) (k X1 X1))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq60647 X0 X1
       have i₂ := eq15960 X0 (M.op X0 (M.op sF3 sF4)) (k X1 X1)
       grind)
    | (have i₁ := eq60647 X1 X1
       have i₂ := eq15960 (M.op X1 (M.op sF3 sF4)) X1 (k X1 X1)
       grind)
    | exact superpose eq15960 eq60647
    | exact resolve eq60647 eq15960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60647
  have eq60779 : ∀ X1 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (k X1 X1)) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq60724 x X1
       have i₂ := eq30812 (k X1 X1) (M.op sF3 sF4) x
       grind)
    | exact superpose eq30812 eq60724
    | exact resolve eq60724 eq30812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60724
  have eq63138 : ∀ X0 X1 : G, (M.op (M.op (M.op y (M.op x y)) (M.op X0 (τ (k X1 X1)))) (M.op x y)) = X0 ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq43593 eq16
    | exact resolve eq16 eq43593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43593
  have eq63195 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op (M.op y (M.op x y)) (τ (k X1 X1)))) X0) = X0 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq63138 X1 X1
       have i₂ := eq15926 (M.op y sF0) X1 (τ (k X1 X1)) sF0
       grind)
    | (have i₁ := eq63138 X0 X1
       have i₂ := eq15926 X0 sF0 (τ (k X1 X1)) (M.op y sF0)
       grind)
    | exact superpose eq15926 eq63138
    | exact resolve eq63138 eq15926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63138
  have eq63231 : ∀ X0 X1 : G, (M.op (τ (k X1 X1)) X0) = X0 ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq37464 eq63195
    | exact resolve eq63195 eq37464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37464 eq63195
  have eq63738 : ∀ X0 : G, (σ x) = (M.op (M.op (τ (k X0 X0)) (M.op (σ x) (σ y))) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq175 (τ (k x x))
       have i₂ := eq63231 sF3 x
       grind)
    | exact superpose eq63231 eq175
    | exact resolve eq175 eq63231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63792 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (τ (k X0 X0))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq58027 eq63738
    | exact resolve eq63738 eq58027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58027 eq63738
  have eq68447 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (τ (k X0 X0)) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq63792 eq586
    | exact resolve eq586 eq63792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq68480 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (τ (k X0 X0))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq68447 X0
       have i₂ := eq15926 sF2 (τ (k X0 X0)) sF3 (M.op sF2 sF4)
       grind)
    | (have i₁ := eq68447 X0
       have i₂ := eq15926 (τ (k X0 X0)) (M.op sF2 sF4) sF3 sF2
       grind)
    | exact superpose eq15926 eq68447
    | exact resolve eq68447 eq15926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15926 eq68447
  have eq68519 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ x) (τ (k X0 X0))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq175 eq68480
    | exact resolve eq68480 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68480
  have eq195071 : ∀ X0 : G, (M.op X0 X0) = (M.op (k y (M.op x y)) (k (σ y) (σ x))) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq47558 eq31764
    | exact resolve eq31764 eq47558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31764 eq47558
  have eq195429 : ∀ X0 : G, (M.op X0 X0) = (M.op (k y (M.op x y)) (k (σ y) (σ x))) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq195071 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195071
  have eq195602 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq31680 eq195429
    | exact resolve eq195429 eq31680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31680 eq195429
  have eq196240 : (σ x) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (k (σ y) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq175 sF3
       have i₂ := eq195602 sF3
       grind)
    | exact superpose eq195602 eq175
    | exact resolve eq175 eq195602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196319 : ∀ X0 : G, (k (σ y) (σ x)) = (τ (k X0 X0)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq63231 (τ (k X0 X0)) X0
       have i₂ := eq195602 (τ (k X0 X0))
       grind)
    | exact superpose eq195602 eq63231
    | exact resolve eq63231 eq195602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63231 eq195602
  have eq196428 : ∀ X0 : G, (k (σ y) (σ x)) = (τ (k X0 X0)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq196319 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196319
  have eq196982 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ x) (k (σ y) (σ x))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq68519 x
       have i₂ := eq196428 x
       grind)
    | exact superpose eq196428 eq68519
    | exact resolve eq68519 eq196428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68519 eq196428
  have eq197006 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ x) (k (σ y) (σ x))) ∨ x = y := by grind
  clear eq196982
  have eq197602 : (σ x) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq692 eq196240
    | exact resolve eq196240 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692 eq196240
  have eq197730 : (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq197602
       have i₂ := eq15962 sF3 sF4
       grind)
    | exact superpose eq15962 eq197602
    | exact resolve eq197602 eq15962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197602
  have eq197759 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq890 eq197730
    | exact resolve eq197730 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890 eq197730
  have eq198739 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (σ y)) (k X0 X0)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq197759 eq60779
    | exact resolve eq60779 eq197759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60779
  have eq198746 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (σ y)) (τ (k X0 X0))) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq197759 eq63792
    | exact resolve eq63792 eq197759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63792
  have eq198767 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (σ y)) (k X0 X0)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq198739 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198739
  have eq198786 : ∀ X0 : G, (σ x) = (τ (k X0 X0)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq198746 X0
       have i₂ := eq15961 (τ (k X0 X0)) sF3
       grind)
    | exact superpose eq15961 eq198746
    | exact resolve eq198746 eq15961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198746
  have eq198788 : ∀ X0 : G, (σ x) = (k X0 X0) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq198767 X0
       have i₂ := eq15961 (k X0 X0) sF3
       grind)
    | exact superpose eq15961 eq198767
    | exact resolve eq198767 eq15961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198767
  have eq198808 : ∀ X0 : G, (σ x) = (τ (k X0 X0)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq865 eq198786
    | (have j0 := eq198786 X0
       grind)
    | exact resolve eq198786 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198786
  have eq198809 : ∀ X0 : G, (σ x) = (τ (k X0 X0)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq198808 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198808
  have eq198818 : (σ x) = (τ (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq198788 eq198809
    | exact resolve eq198809 eq198788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198788 eq198809
  have eq198821 : x = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq198818
    | exact resolve eq198818 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198818
  have eq198823 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq865 eq198821
    | exact resolve eq198821 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198821
  have eq198833 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq198823 eq27
    | exact resolve eq27 eq198823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198823
  have eq198943 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ x) ∨ x = y := by
    first
    | exact superpose eq6687 eq198833
    | (have r₁ := eq198833
       have r₂ := eq6687
       grind)
    | exact resolve eq198833 eq6687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6687 eq198833
  have eq198947 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ x = y := by grind
  clear eq198943
  have eq198949 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ x = y := by
    first
    | exact superpose eq198947 eq31
    | exact resolve eq31 eq198947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198947
  have eq199153 : x = y ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ x = y := by
    first
    | exact superpose eq29 eq198949
    | exact resolve eq198949 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198949
  have eq199154 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq199153
  have eq199175 : x = (τ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq199154 eq29
    | exact resolve eq29 eq199154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq199330 : y = (M.op (M.op (M.op x y) (k (σ y) (M.op x y))) (M.op x y)) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq199154 eq43875
    | exact resolve eq43875 eq199154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43875
  have eq199366 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op x y) (k (σ y) (M.op x y))) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq199154 eq197006
    | exact resolve eq197006 eq199154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197006
  have eq199367 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op x y) (k (σ y) (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq199366
  have eq199397 : y = (M.op (M.op (M.op x y) (k (σ y) (M.op x y))) (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq199330
  have eq199442 : y = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq199367 eq199397
    | exact resolve eq199397 eq199367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199367 eq199397
  have eq199465 : (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2249 eq199175
    | exact resolve eq199175 eq2249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2249 eq199175
  have eq199471 : y = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq38839 eq199442
    | exact resolve eq199442 eq38839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38839 eq199442
  have eq199492 : (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8772 eq199465
    | exact resolve eq199465 eq8772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8772 eq199465
  have eq199493 : (M.op x y) = (τ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq199492
  have eq199512 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq199493 eq14
    | exact resolve eq14 eq199493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199513 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq199512
    | exact resolve eq199512 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199512
  have eq201366 : y = (M.op (M.op (M.op x y) (σ y)) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq197759 eq199471
    | exact resolve eq199471 eq197759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197759 eq199471
  have eq201489 : y = (M.op (M.op (M.op x y) (σ y)) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq201366
  have eq201538 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq201489
       have i₂ := eq15962 sF0 sF3
       grind)
    | exact superpose eq15962 eq201489
    | exact resolve eq201489 eq15962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15962 eq201489
  have eq201539 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq201538
  have eq201574 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq865 eq201539
    | exact resolve eq201539 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865 eq201539
  have eq201575 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq201574
  have eq201637 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq201575 eq27
    | exact resolve eq27 eq201575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201575
  have eq201719 : (M.op x y) ≠ (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq199513 eq201637
    | exact resolve eq201637 eq199513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199513 eq201637
  have eq201755 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq199154 eq201719
    | (have r₁ := eq201719
       have r₂ := eq199154
       grind)
    | exact resolve eq201719 eq199154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199154 eq201719
  have eq201756 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq201755
  have eq201757 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq201756
  have eq201760 : y = (τ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq201757 eq31
    | exact resolve eq31 eq201757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq201757
  have eq201991 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq199493 eq201760
    | exact resolve eq201760 eq199493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199493 eq201760
  have eq201992 : y = (M.op x y) ∨ x = y := by grind
  clear eq201991
  have eq202092 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq201992
  have eq202094 : x = y := by
    first
    | (have r₁ := eq202092
       have r₂ := eq6665
       grind)
    | exact resolve eq202092 eq6665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6665 eq202092
  have eq202109 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq202094
       grind)
    | exact superpose eq202094 eq24
    | exact resolve eq24 eq202094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq202112 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq202094
       grind)
    | exact superpose eq202094 eq174
    | exact resolve eq174 eq202094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq202117 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op (M.op X1 x) (M.op X0 x))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq581 X0 X1
       have i₂ := eq202094
       grind)
    | exact superpose eq202094 eq581
    | exact resolve eq581 eq202094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581 eq202094
  have eq202219 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq202117 X0 X1
       have i₂ := eq15927 X0 X1 x
       grind)
    | exact superpose eq15927 eq202117
    | exact resolve eq202117 eq15927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202117
  have eq202223 : ∀ X0 : G, x = (M.op X0 (M.op (M.op X0 (M.op x y)) x)) := by
    intro X0
    first
    | (have i₁ := eq202112 X0
       have i₂ := eq15960 X0 (M.op X0 sF0) x
       grind)
    | (have i₁ := eq202112 x
       have i₂ := eq15960 (M.op x sF0) x x
       grind)
    | exact superpose eq15960 eq202112
    | exact resolve eq202112 eq15960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202112
  have eq202226 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq202109
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq202109
    | exact resolve eq202109 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202109
  have eq202239 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 (M.op x y)) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq202219 X0 x
       have i₂ := eq15960 X0 (M.op X0 sF0) x
       grind)
    | (have i₁ := eq202219 X1 x
       have i₂ := eq15960 (M.op X1 sF0) X1 x
       grind)
    | exact superpose eq15960 eq202219
    | exact resolve eq202219 eq15960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202219
  have eq202243 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq202223 x
       have i₂ := eq30812 x sF0 x
       grind)
    | exact superpose eq30812 eq202223
    | exact resolve eq202223 eq30812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202223
  have eq202252 : ∀ X1 : G, (M.op (M.op x y) X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq202239 x x
       have i₂ := eq30812 x sF0 x
       grind)
    | exact superpose eq30812 eq202239
    | exact resolve eq202239 eq30812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202239
  have eq202278 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq202226 eq175
    | exact resolve eq175 eq202226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq202338 : (σ x) = (M.op (M.op (σ x) (σ x)) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq202226 eq9400
    | exact resolve eq9400 eq202226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9400 eq202226
  have eq202402 : (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq202338
       have i₂ := eq15961 sF0 sF2
       grind)
    | exact superpose eq15961 eq202338
    | exact resolve eq202338 eq15961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15961 eq202338
  have eq202428 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq202278 X0
       have i₂ := eq15960 X0 (M.op X0 sF4) sF2
       grind)
    | (have i₁ := eq202278 x
       have i₂ := eq15960 (M.op x sF4) x sF2
       grind)
    | exact superpose eq15960 eq202278
    | exact resolve eq202278 eq15960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15960 eq202278
  have eq202455 : x = (M.op x y) := by
    first
    | (have r₁ := eq202402
       have r₂ := eq8802
       grind)
    | exact resolve eq202402 eq8802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8802 eq202402
  have eq202473 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq202428 x
       have i₂ := eq30812 sF2 sF4 x
       grind)
    | exact superpose eq30812 eq202428
    | exact resolve eq202428 eq30812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30812 eq202428
  have eq202488 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq202455
       grind)
    | exact superpose eq202455 eq22
    | exact resolve eq22 eq202455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq202455
  have eq202731 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq202488 eq20
    | exact resolve eq20 eq202488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202488
  have eq203219 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq202243 eq16
    | exact resolve eq16 eq202243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202243
  have eq203308 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq203219 X0
       have i₂ := eq15927 X0 X0 x
       grind)
    | exact superpose eq15927 eq203219
    | exact resolve eq203219 eq15927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203219
  have eq203552 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op x y) = X0 ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq202252 eq12
    | (have j0 := eq12 X0 (M.op x y)
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq202252 x
       grind)
    | exact resolve eq12 eq202252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203553 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq202252 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq202252 (M.op x y)
       grind)
    | exact resolve eq13 eq202252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202252
  have eq203822 : ∀ X0 : G, (M.op x y) = X0 ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq203552 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203552
  have eq203891 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) ∨ (M.op x y) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq203553 X0
       have i₂ := eq203308 X0
       grind)
    | exact superpose eq203308 eq203553
    | (have j0 := eq203553 X0
       grind)
    | (have r₁ := eq203553 (M.op X0 X0)
       have r₂ := eq203308 X0
       grind)
    | exact resolve eq203553 eq203308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203553
  have eq203929 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq203891 X0
       have j1 := eq203822 (k X0 (M.op x y))
       grind)
    | (have r₁ := eq203891 X0
       have r₂ := eq203822 X0
       grind)
    | (have r₁ := eq203891 (M.op x y)
       have r₂ := eq203822 (M.op x y)
       grind)
    | (have r₁ := eq203891 (k X0 (M.op x y))
       have r₂ := eq203822 X0
       grind)
    | exact resolve eq203891 eq203822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203822 eq203891
  have eq204209 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq202473 eq16
    | exact resolve eq16 eq202473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202473
  have eq204297 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq204209 X0
       have i₂ := eq15927 X0 X0 sF2
       grind)
    | exact superpose eq15927 eq204209
    | exact resolve eq204209 eq15927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15927 eq204209
  have eq204316 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq204297 x
       have i₂ := eq203308 x
       grind)
    | exact superpose eq203308 eq204297
    | exact resolve eq204297 eq203308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204297
  have eq204333 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq204316 eq27
    | exact resolve eq27 eq204316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq204316
  have eq204406 : (M.op x y) ≠ (σ x) := by
    first
    | exact superpose eq202731 eq204333
    | exact resolve eq204333 eq202731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204333
  have eq205089 : ∀ X0 : G, (M.op x y) = (k X0 X0) ∨ (M.op x y) = X0 ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq203308 X0
       grind)
    | exact superpose eq203308 eq11
    | exact resolve eq11 eq203308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205091 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op x y) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq203308 X0
       grind)
    | exact superpose eq203308 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq203308 (M.op x y)
       grind)
    | exact resolve eq13 eq203308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203308
  have eq205468 : ∀ X0 : G, (M.op x y) = (k X0 X0) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have j0 := eq205089 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205089
  have eq205537 : ∀ X0 : G, (M.op x y) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq205468 X0
       have j1 := eq205091 X0
       grind)
    | (have r₁ := eq205468 X0
       have r₂ := eq205091 (k X0 X0)
       grind)
    | (have r₁ := eq205468 X0
       have r₂ := eq205091 X0
       grind)
    | (have r₁ := eq205468 (M.op x y)
       have r₂ := eq205091 (M.op x y)
       grind)
    | exact resolve eq205468 eq205091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205091 eq205468
  have eq205704 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq203929 eq35
    | exact resolve eq35 eq203929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq203929
  have eq205801 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq205704
    | exact resolve eq205704 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq205704
  have eq205806 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq202731 eq205801
    | exact resolve eq205801 eq202731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202731 eq205801
  have eq205810 : (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq205806
       have i₂ := eq205537 sF2
       grind)
    | exact superpose eq205537 eq205806
    | exact resolve eq205806 eq205537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205537 eq205806
  have eq205812 : False := by grind
  exact eq205812

/-- `Equation2646`: `x = ((x ◇ x) ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2646 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2646 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2646.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
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
  clear eq35
  have eq50 : y ≠ (M.op x y) ∨ x = (k x y) := by
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
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
  have eq67 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (k x y) := by
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
  have eq68 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq98
    | exact resolve eq98 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq102 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq127 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq144 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq127 eq16
    | exact resolve eq16 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq592 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq592
    | exact resolve eq592 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq596 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq593
       have r₂ := eq27
       grind)
    | exact resolve eq593 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq598 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq596
    | exact resolve eq596 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq600 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq598
    | exact resolve eq598 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq668 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq600 eq51
    | (have r₁ := eq51
       have r₂ := eq600
       grind)
    | exact resolve eq51 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq671 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq668
  have eq675 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq671 eq55
    | exact resolve eq55 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq683 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq675
    | exact resolve eq675 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq675
  have eq687 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq683
       have r₂ := eq50
       grind)
    | exact resolve eq683 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq690 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq687
       grind)
    | exact superpose eq687 eq44
    | exact resolve eq44 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq687
       grind)
    | exact superpose eq687 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq692 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq691
  have eq694 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq692
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq692
    | exact resolve eq692 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq695 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq694
  have eq696 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq690
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq690
    | exact resolve eq690 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq699 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq695
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq695
    | exact resolve eq695 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq715 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq699 eq68
    | (have r₁ := eq68
       have r₂ := eq699
       grind)
    | exact resolve eq68 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq717 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq699 eq51
    | exact resolve eq51 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq718 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq699 eq27
    | exact resolve eq27 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq719 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq715
  have eq729 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq696 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq730 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq729
  have eq734 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq730
    | exact resolve eq730 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq735 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq734
  have eq740 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq735
    | exact resolve eq735 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq742 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq740 eq27
    | exact resolve eq27 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq764 : (τ (σ y)) = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq719 eq55
    | exact resolve eq55 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq719
  have eq775 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq764
    | exact resolve eq764 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq764
  have eq780 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq775
       have r₂ := eq67
       grind)
    | exact resolve eq775 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq788 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq780
       grind)
    | exact superpose eq780 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq789 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq788
  have eq791 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq789
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq789
    | exact resolve eq789 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq792 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq791
  have eq797 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq792
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq792
    | exact resolve eq792 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq792
  have eq805 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq797 eq103
    | exact resolve eq103 eq797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq813 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq797 eq717
    | (have r₁ := eq717
       have r₂ := eq797
       grind)
    | exact resolve eq717 eq797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717 eq797
  have eq819 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq813
  have eq820 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq819
  have eq826 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq805
  have eq1081 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq826 eq820
    | exact resolve eq820 eq826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820 eq826
  have eq1085 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1081
  have eq1089 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1085
       have r₂ := eq718
       grind)
    | exact resolve eq1085 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718 eq1085
  have eq1091 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1089 eq20
    | exact resolve eq20 eq1089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1093 : y ≠ y ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1089 eq50
    | (have r₁ := eq50
       have r₂ := eq1089
       grind)
    | exact resolve eq50 eq1089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089
  have eq1105 : x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq1093
  have eq1115 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1091
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1091
    | exact resolve eq1091 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq1162 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1115 eq26
    | exact resolve eq26 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1178 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1115 eq742
    | (have r₁ := eq742
       have r₂ := eq1115
       grind)
    | exact resolve eq742 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq1184 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1178
  have eq1185 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1184
  have eq1250 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1185 eq27
    | exact resolve eq27 eq1185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1261 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1105
       grind)
    | exact superpose eq1105 eq44
    | exact resolve eq44 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq1267 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1261
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1261
    | exact resolve eq1261 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261
  have eq1325 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1162 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1162
       grind)
    | exact resolve eq12 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq1328 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1325
       have r₂ := eq1185
       grind)
    | exact resolve eq1325 eq1185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185 eq1325
  have eq1329 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1328
       have r₂ := eq27
       grind)
    | exact resolve eq1328 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328
  have eq1330 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1115 eq1267
    | exact resolve eq1267 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115 eq1267
  have eq1352 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq1330
  have eq1414 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1352 eq1329
    | exact resolve eq1329 eq1352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329 eq1352
  have eq1418 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1414
  have eq1422 : x = (M.op x y) := by
    first
    | (have r₁ := eq1418
       have r₂ := eq1250
       grind)
    | exact resolve eq1418 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250 eq1418
  have eq1426 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1422 eq20
    | exact resolve eq20 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1428 : x ≠ y ∨ x = (k x y) := by
    first
    | exact superpose eq1422 eq50
    | exact resolve eq50 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1430 : x ≠ x ∨ x = y ∨ y = (k x y) := by
    first
    | exact superpose eq1422 eq67
    | (have r₁ := eq67
       have r₂ := eq1422
       grind)
    | exact resolve eq67 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq1441 : y = (k x y) ∨ x = y := by grind
  clear eq1430
  have eq1453 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1426
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1426
    | exact resolve eq1426 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426
  have eq1510 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1453 eq26
    | exact resolve eq26 eq1453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1705 : (σ y) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq1441
       grind)
    | exact superpose eq1441 eq44
    | exact resolve eq44 eq1441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1441
  have eq1714 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1453 eq1705
    | exact resolve eq1705 eq1453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1705
  have eq1718 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1714
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1714
    | exact resolve eq1714 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1714
  have eq1728 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1718 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq11 eq1718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1729 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by grind
  clear eq1728
  have eq1732 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1510 eq1729
    | exact resolve eq1729 eq1510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1729
  have eq1735 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1510 eq1732
    | exact resolve eq1732 eq1510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1732
  have eq1738 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq1735
       have r₂ := eq27
       grind)
    | exact resolve eq1735 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1735
  have eq1743 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq1738 eq27
    | exact resolve eq27 eq1738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1744 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1738 eq51
    | (have r₁ := eq51
       have r₂ := eq1738
       grind)
    | exact resolve eq51 eq1738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1738
  have eq1751 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq1744
  have eq1755 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1453 eq1751
    | exact resolve eq1751 eq1453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751
  have eq1904 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1755 eq1718
    | exact resolve eq1718 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1718
  have eq1905 : (τ (σ (M.op x y))) = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq1755 eq144
    | exact resolve eq144 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq1755
  have eq1908 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1904
  have eq1913 : (τ (σ (M.op x y))) = (k x y) ∨ x = y := by
    first
    | exact superpose eq1422 eq1905
    | exact resolve eq1905 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1905
  have eq1914 : x = y := by
    first
    | (have r₁ := eq1908
       have r₂ := eq1743
       grind)
    | exact resolve eq1908 eq1743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743 eq1908
  have eq1918 : (M.op x y) = (k x y) ∨ x = y := by
    first
    | exact superpose eq30 eq1913
    | exact resolve eq1913 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1913
  have eq1921 : x = (k x y) ∨ x = y := by
    first
    | exact superpose eq1422 eq1918
    | exact resolve eq1918 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422 eq1918
  have eq1923 : x = (k x y) := by
    first
    | (have r₁ := eq1921
       have r₂ := eq1428
       grind)
    | exact resolve eq1921 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428 eq1921
  have eq1925 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1914
       grind)
    | exact superpose eq1914 eq24
    | exact resolve eq24 eq1914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1957 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1925
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1925
    | exact resolve eq1925 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1925
  have eq1970 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1453 eq1957
    | exact resolve eq1957 eq1453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957
  have eq2142 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1970 eq1510
    | exact resolve eq1510 eq1970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1510 eq1970
  have eq2166 : x = (k x x) := by
    first
    | (have i₁ := eq1923
       have i₂ := eq1914
       grind)
    | exact superpose eq1914 eq1923
    | exact resolve eq1923 eq1914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1914 eq1923
  have eq2168 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq2166
       grind)
    | exact superpose eq2166 eq43
    | exact resolve eq43 eq2166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq2166
  have eq2172 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1453 eq2168
    | exact resolve eq2168 eq1453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2168
  have eq2173 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2172
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2172
    | exact resolve eq2172 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2172
  have eq2174 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1453 eq2173
    | exact resolve eq2173 eq1453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1453 eq2173
  have eq2673 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2174 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq2174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174
  have eq2674 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2673
  have eq2690 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2142 eq2674
    | exact resolve eq2674 eq2142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2142 eq2674
  have eq2691 : False := by grind
  exact eq2691

/-- `Equation2646`: `x = ((x ◇ x) ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2646 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2646 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2646.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
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
  have eq66 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k y x) := by
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
  have eq67 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
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
  clear eq36
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
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq98
    | exact resolve eq98 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq100 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq589 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq590 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq589
    | exact resolve eq589 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq593 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq590
       have r₂ := eq27
       grind)
    | exact resolve eq590 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq595 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq593
    | exact resolve eq593 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq597 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq595
    | exact resolve eq595 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq610 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq597 eq67
    | (have r₁ := eq67
       have r₂ := eq597
       grind)
    | exact resolve eq67 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq614 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq597
  have eq615 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq610
  have eq685 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq615
       have r₂ := eq614
       grind)
    | exact resolve eq615 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614 eq615
  have eq689 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq685 eq82
    | exact resolve eq82 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq697 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq689
    | exact resolve eq689 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq689
  have eq701 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq697
       have r₂ := eq66
       grind)
    | exact resolve eq697 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq704 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq701
       grind)
    | exact superpose eq701 eq75
    | exact resolve eq75 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq705 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq701
       grind)
    | exact superpose eq701 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq706 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq705
  have eq708 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq706
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq706
    | exact resolve eq706 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq709 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq708
  have eq710 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq704
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq704
    | exact resolve eq704 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq713 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq709
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq709
    | exact resolve eq709 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq717 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq713 eq51
    | (have r₁ := eq51
       have r₂ := eq713
       grind)
    | exact resolve eq51 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq719 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq717
  have eq740 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq710 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq741 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq740
  have eq745 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq741
    | exact resolve eq741 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq746 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq745
  have eq751 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq746
    | exact resolve eq746 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq796 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq751 eq27
    | exact resolve eq27 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq855 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq719 eq82
    | exact resolve eq82 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq866 : y = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq855
    | exact resolve eq855 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq869 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq866
       have r₂ := eq50
       grind)
    | exact resolve eq866 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq875 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq869
       grind)
    | exact superpose eq869 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq876 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq875
  have eq878 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq876
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq876
    | exact resolve eq876 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq879 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq878
  have eq883 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq879
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq879
    | exact resolve eq879 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq879
  have eq928 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq883 eq20
    | exact resolve eq20 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq932 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq883 eq66
    | (have r₁ := eq66
       have r₂ := eq883
       grind)
    | exact resolve eq66 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq941 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq883
  have eq942 : x = y ∨ x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq932
  have eq953 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq928
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq928
    | exact resolve eq928 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq1016 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq953 eq796
    | (have r₁ := eq796
       have r₂ := eq953
       grind)
    | exact resolve eq796 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796 eq953
  have eq1019 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1016
  have eq1020 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1019
  have eq1040 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1020 eq51
    | (have r₁ := eq51
       have r₂ := eq1020
       grind)
    | exact resolve eq51 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1020
  have eq1042 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1040
  have eq1172 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1042 eq82
    | exact resolve eq82 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq1042
  have eq1187 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1172
    | exact resolve eq1172 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1172
  have eq1190 : y = (k y x) := by
    first
    | (have r₁ := eq1187
       have r₂ := eq50
       grind)
    | exact resolve eq1187 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1187
  have eq1195 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq1190
       grind)
    | exact superpose eq1190 eq75
    | exact resolve eq75 eq1190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq1200 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1195
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1195
    | exact resolve eq1195 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1195
  have eq1213 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1200 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1214 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1213
  have eq1216 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1214
    | exact resolve eq1214 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1219 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1216
    | exact resolve eq1216 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1216
  have eq1273 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1219 eq67
    | (have r₁ := eq67
       have r₂ := eq1219
       grind)
    | exact resolve eq67 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq1276 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1219
  have eq1277 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1273
  have eq1278 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1200 eq1277
    | exact resolve eq1277 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200 eq1277
  have eq1279 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1278
  have eq1332 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1279
       have r₂ := eq1276
       grind)
    | exact resolve eq1279 eq1276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276 eq1279
  have eq1336 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1332 eq27
    | exact resolve eq27 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1332
  have eq2256 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq942
       have r₂ := eq941
       grind)
    | exact resolve eq942 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq2257 : x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2256
       have i₂ := eq1190
       grind)
    | exact superpose eq1190 eq2256
    | exact resolve eq2256 eq1190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190 eq2256
  have eq2258 : x = (M.op x y) := by
    first
    | (have r₁ := eq2257
       have r₂ := eq941
       grind)
    | exact resolve eq2257 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941 eq2257
  have eq2260 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2258 eq20
    | exact resolve eq20 eq2258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2258
  have eq2290 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2260
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2260
    | exact resolve eq2260 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2260
  have eq2292 : False := by grind
  exact eq2292

/-- `Equation2659`: `x = ((x ◇ y) ◇ (x ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pxy_pxy_pxx_pxy_Equation2659 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2659 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2659.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
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
  have eq42 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq35 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq35
    | exact resolve eq35 eq15
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
  have eq56 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq64 (σ X0)
       grind)
    | exact superpose eq64 eq10
    | exact resolve eq10 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq43
    | exact resolve eq43 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq70 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq67
       have i₂ := eq64 sF2
       grind)
    | exact superpose eq64 eq67
    | exact resolve eq67 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq66
    | exact resolve eq66 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq75 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
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
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq75 x y
       grind)
    | exact superpose eq75 eq44
    | (have j1 := eq75 x y
       grind)
    | exact resolve eq44 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq85
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq85
    | exact resolve eq85 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq90
    | exact resolve eq90 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq92
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq92
    | exact resolve eq92 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq99 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq100 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq24
  have eq102 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (M.op (σ y) (σ X0)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq75 sF3 (σ X0)
       grind)
    | exact superpose eq75 eq36
    | (have j1 := eq75 (σ y) (σ X0)
       grind)
    | exact resolve eq36 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq104 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq100
       have i₂ := eq64 sF3
       grind)
    | exact superpose eq64 eq100
    | exact resolve eq100 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq106 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq64 y
       grind)
    | exact superpose eq64 eq104
    | exact resolve eq104 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq104
  have eq113 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq99
       grind)
    | exact superpose eq99 eq16
    | exact resolve eq16 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq120 : (M.op x y) ≠ (M.op x x) ∨ (M.op y x) = (M.op y y) ∨ (k x y) = (M.op x x) := by
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
  have eq121 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq106
       grind)
    | exact superpose eq106 eq16
    | exact resolve eq16 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k x (τ X0))
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq16
    | exact resolve eq16 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq375 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq655 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq375 X0 X1
       have i₂ := eq75 (σ X0) X1
       grind)
    | exact superpose eq75 eq375
    | (have j1 := eq75 (σ X0) X1
       grind)
    | exact resolve eq375 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq681 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq655 X0 X1
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq655
    | (have j0 := eq655 X0 X1
       grind)
    | exact resolve eq655 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq655
  have eq692 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq93 eq75
    | (have j0 := eq75 (σ x) (σ y)
       grind)
    | exact resolve eq75 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq693 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq692
    | exact resolve eq692 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq696 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq693
       have r₂ := eq27
       grind)
    | exact resolve eq693 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq698 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq696
    | exact resolve eq696 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq700 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq698 eq121
    | (have r₁ := eq121
       have r₂ := eq698
       grind)
    | exact resolve eq121 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq701 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq698 eq63
    | (have r₁ := eq63
       have r₂ := eq698
       grind)
    | exact resolve eq63 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq698
  have eq710 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq701
  have eq711 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq700
  have eq815 : (k y x) = (τ (M.op (σ y) (σ x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq710 eq113
    | exact resolve eq113 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq710
  have eq917 : (M.op y y) = (τ (M.op (σ y) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq711 eq127
    | exact resolve eq127 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq711
  have eq1395 : (k y x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq917 eq815
    | exact resolve eq815 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815 eq917
  have eq1415 : (k y x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1395
  have eq3618 : ∀ X0 : G, (σ (k y X0)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ X0) (σ y)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ X0)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq102 eq13
    | (have j0 := eq13 (σ X0) (σ y)
       have j1 := eq102 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ y)
       have r₂ := eq102 X0
       grind)
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq102 y
       grind)
    | exact resolve eq13 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq3621 : ∀ X0 : G, (σ (k y X0)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ X0) (σ y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3618 X0
       have j1 := eq13 (σ X0) (σ y)
       grind)
    | (have r₁ := eq3618 X0
       have r₂ := eq13 (σ X0) (σ y)
       grind)
    | (have r₁ := eq3618 y
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq3618 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3618
  have eq3632 : ∀ X0 : G, (σ (k y X0)) ≠ (M.op (σ y) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq40 eq3621
    | (have j0 := eq3621 X0
       grind)
    | exact resolve eq3621 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq3621
  have eq61065 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq3632 x
       have i₂ := eq1415
       grind)
    | exact superpose eq1415 eq3632
    | (have j0 := eq3632 x
       grind)
    | exact resolve eq3632 eq1415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415 eq3632
  have eq61125 : (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq61065
       have r₂ := eq106
       grind)
    | exact resolve eq61065 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq61065
  have eq61156 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq61125
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq61125
    | exact resolve eq61125 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61125
  have eq61171 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq61156
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq61156
    | exact resolve eq61156 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq61156
  have eq61181 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq61171
    | exact resolve eq61171 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61171
  have eq61182 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq61181
  have eq61194 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq61182 eq93
    | exact resolve eq93 eq61182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq61182
  have eq61220 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq61194
  have eq61224 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq61220
       have r₂ := eq27
       grind)
    | exact resolve eq61220 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61220
  have eq61230 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq61224
       grind)
    | exact superpose eq61224 eq70
    | exact resolve eq70 eq61224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61232 : (M.op x y) ≠ (M.op x y) ∨ (M.op y x) = (M.op y y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq120
       have i₂ := eq61224
       grind)
    | exact superpose eq61224 eq120
    | (have r₁ := eq120
       have r₂ := eq61224
       grind)
    | exact resolve eq120 eq61224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq61224
  have eq61259 : (M.op y x) = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
  clear eq61232
  have eq61275 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq61230
    | exact resolve eq61230 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61230
  have eq63788 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (k X0 y) = (M.op X0 y) ∨ (M.op x y) = (k x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq61259
       grind)
    | exact superpose eq61259 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq61259
       grind)
    | exact resolve eq13 eq61259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61259
  have eq143140 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op (σ x) X0)) ∨ (σ (M.op x x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq681 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq681
    | (have j0 := eq681 x X0
       grind)
    | exact resolve eq681 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq681
  have eq143365 : ∀ X0 : G, (τ (k (σ x) X0)) = (τ (M.op (σ x) X0)) ∨ (σ (M.op x x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq143140 X0
       have i₂ := eq252 X0
       grind)
    | exact superpose eq252 eq143140
    | (have j0 := eq143140 X0
       grind)
    | exact resolve eq143140 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq143140
  have eq143418 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (τ (k (σ x) X0)) = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq143365 X0
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq143365
    | (have j0 := eq143365 X0
       grind)
    | exact resolve eq143365 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq143365
  have eq143452 : ∀ X0 : G, (τ (k (σ x) X0)) = (τ (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq61275 eq143418
    | (have j0 := eq143418 X0
       grind)
    | exact resolve eq143418 eq61275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61275 eq143418
  have eq143619 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq143452 eq56
    | (have j1 := eq143452 (σ y)
       grind)
    | exact resolve eq56 eq143452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq143452
  have eq143986 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq143619
    | exact resolve eq143619 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143619
  have eq143993 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq143986
    | exact resolve eq143986 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq143986
  have eq143996 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq143993
       have r₂ := eq27
       grind)
    | exact resolve eq143993 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143993
  have eq532874 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq63788 X0
       have i₂ := eq143996
       grind)
    | exact superpose eq143996 eq63788
    | (have j0 := eq63788 X0
       grind)
    | exact resolve eq63788 eq143996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63788
  have eq532877 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x y) := by
    first
    | (have j0 := eq532874 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532874
  have eq532880 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq532877
       have i₂ := eq143996
       grind)
    | exact superpose eq143996 eq532877
    | exact resolve eq532877 eq143996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143996 eq532877
  have eq532882 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq532880
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq532880
    | exact resolve eq532880 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq532880
  have eq532883 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq532882
  have eq532902 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq532883 eq15
    | exact resolve eq15 eq532883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532883
  have eq533320 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq532902
    | exact resolve eq532902 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq532902
  have eq533331 : False := by grind
  exact eq533331

/-- `Equation2665`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2665 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2665 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2665.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
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
  clear eq35
  have eq50 : y ≠ (M.op x y) ∨ x = (k x y) := by
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
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
  have eq70 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (k x y) := by
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
  have eq71 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq101
    | exact resolve eq101 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq105 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq103
    | exact resolve eq103 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq130 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq147 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq130 eq16
    | exact resolve eq16 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq701 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq106 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq701
    | exact resolve eq701 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq705 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq702
       have r₂ := eq27
       grind)
    | exact resolve eq702 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq707 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq705
    | exact resolve eq705 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq709 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq707
    | exact resolve eq707 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq712 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq709 eq51
    | (have r₁ := eq51
       have r₂ := eq709
       grind)
    | exact resolve eq51 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq718 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq712
  have eq751 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq718 eq55
    | exact resolve eq55 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq759 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq751
    | exact resolve eq751 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq751
  have eq763 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq759
       have r₂ := eq50
       grind)
    | exact resolve eq759 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq766 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq763
       grind)
    | exact superpose eq763 eq44
    | exact resolve eq44 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq767 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq763
       grind)
    | exact superpose eq763 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq768 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq767
  have eq770 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq768
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq768
    | exact resolve eq768 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq771 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq770
  have eq772 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq766
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq766
    | exact resolve eq766 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq775 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq771
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq771
    | exact resolve eq771 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq778 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq775 eq27
    | exact resolve eq27 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq779 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq775 eq51
    | exact resolve eq51 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq782 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq775 eq71
    | (have r₁ := eq71
       have r₂ := eq775
       grind)
    | exact resolve eq71 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq775
  have eq785 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq782
  have eq824 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq772 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq825 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq824
  have eq829 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq825
    | exact resolve eq825 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq830 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq829
  have eq835 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq830
    | exact resolve eq830 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq842 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq835 eq27
    | exact resolve eq27 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq901 : (τ (σ y)) = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq785 eq55
    | exact resolve eq55 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq785
  have eq912 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq901
    | exact resolve eq901 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq901
  have eq917 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq912
       have r₂ := eq70
       grind)
    | exact resolve eq912 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq925 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq917
       grind)
    | exact superpose eq917 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq926 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq925
  have eq928 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq926
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq926
    | exact resolve eq926 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926
  have eq929 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq928
  have eq934 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq929
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq929
    | exact resolve eq929 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq929
  have eq942 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq934 eq106
    | exact resolve eq106 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq950 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq934 eq779
    | (have r₁ := eq779
       have r₂ := eq934
       grind)
    | exact resolve eq779 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779 eq934
  have eq958 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq950
  have eq959 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq958
  have eq965 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq942
  have eq1108 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq965 eq959
    | exact resolve eq959 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959 eq965
  have eq1112 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1108
  have eq1116 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1112
       have r₂ := eq778
       grind)
    | exact resolve eq1112 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778 eq1112
  have eq1118 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1116 eq20
    | exact resolve eq20 eq1116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1120 : y ≠ y ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1116 eq50
    | (have r₁ := eq50
       have r₂ := eq1116
       grind)
    | exact resolve eq50 eq1116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1135 : x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq1120
  have eq1144 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1118
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1118
    | exact resolve eq1118 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118
  have eq1188 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1144 eq26
    | exact resolve eq26 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1204 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1144 eq842
    | (have r₁ := eq842
       have r₂ := eq1144
       grind)
    | exact resolve eq842 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq1212 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1204
  have eq1213 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1212
  have eq1233 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1213 eq27
    | exact resolve eq27 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1290 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1135
       grind)
    | exact superpose eq1135 eq44
    | exact resolve eq44 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq1296 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1290
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1290
    | exact resolve eq1290 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq1306 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1188 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1188
       grind)
    | exact resolve eq12 eq1188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1306
       have r₂ := eq1213
       grind)
    | exact resolve eq1306 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213 eq1306
  have eq1317 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1316
       have r₂ := eq27
       grind)
    | exact resolve eq1316 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316
  have eq1318 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1144 eq1296
    | exact resolve eq1296 eq1144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144 eq1296
  have eq1340 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq1318
  have eq1402 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1340 eq1317
    | exact resolve eq1317 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1317 eq1340
  have eq1406 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1402
  have eq1410 : x = (M.op x y) := by
    first
    | (have r₁ := eq1406
       have r₂ := eq1233
       grind)
    | exact resolve eq1406 eq1233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233 eq1406
  have eq1414 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1410 eq20
    | exact resolve eq20 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1416 : x ≠ y ∨ x = (k x y) := by
    first
    | exact superpose eq1410 eq50
    | exact resolve eq50 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1419 : x ≠ x ∨ x = y ∨ y = (k x y) := by
    first
    | exact superpose eq1410 eq70
    | (have r₁ := eq70
       have r₂ := eq1410
       grind)
    | exact resolve eq70 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq1432 : y = (k x y) ∨ x = y := by grind
  clear eq1419
  have eq1443 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1414
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1414
    | exact resolve eq1414 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414
  have eq1498 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1443 eq26
    | exact resolve eq26 eq1443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1786 : (σ y) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq1432
       grind)
    | exact superpose eq1432 eq44
    | exact resolve eq44 eq1432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1432
  have eq1795 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1443 eq1786
    | exact resolve eq1786 eq1443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786
  have eq1799 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1795
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1795
    | exact resolve eq1795 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795
  have eq1809 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1799 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq11 eq1799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1810 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by grind
  clear eq1809
  have eq1813 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1498 eq1810
    | exact resolve eq1810 eq1498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1810
  have eq1816 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1498 eq1813
    | exact resolve eq1813 eq1498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1813
  have eq1819 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq1816
       have r₂ := eq27
       grind)
    | exact resolve eq1816 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1816
  have eq1824 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq1819 eq27
    | exact resolve eq27 eq1819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1825 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1819 eq51
    | (have r₁ := eq51
       have r₂ := eq1819
       grind)
    | exact resolve eq51 eq1819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1819
  have eq1837 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq1825
  have eq1845 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1443 eq1837
    | exact resolve eq1837 eq1443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1837
  have eq1868 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1845 eq1799
    | exact resolve eq1799 eq1845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1799
  have eq1869 : (τ (σ (M.op x y))) = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq1845 eq147
    | exact resolve eq147 eq1845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq1845
  have eq1872 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1868
  have eq1877 : (τ (σ (M.op x y))) = (k x y) ∨ x = y := by
    first
    | exact superpose eq1410 eq1869
    | exact resolve eq1869 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869
  have eq1878 : x = y := by
    first
    | (have r₁ := eq1872
       have r₂ := eq1824
       grind)
    | exact resolve eq1872 eq1824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1824 eq1872
  have eq1882 : (M.op x y) = (k x y) ∨ x = y := by
    first
    | exact superpose eq30 eq1877
    | exact resolve eq1877 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1877
  have eq1885 : x = (k x y) ∨ x = y := by
    first
    | exact superpose eq1410 eq1882
    | exact resolve eq1882 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410 eq1882
  have eq1887 : x = (k x y) := by
    first
    | (have r₁ := eq1885
       have r₂ := eq1416
       grind)
    | exact resolve eq1885 eq1416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1416 eq1885
  have eq1889 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1878
       grind)
    | exact superpose eq1878 eq24
    | exact resolve eq24 eq1878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1919 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1889
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1889
    | exact resolve eq1889 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1889
  have eq1931 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1443 eq1919
    | exact resolve eq1919 eq1443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1919
  have eq2041 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1931 eq1498
    | exact resolve eq1498 eq1931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498 eq1931
  have eq2065 : x = (k x x) := by
    first
    | (have i₁ := eq1887
       have i₂ := eq1878
       grind)
    | exact superpose eq1878 eq1887
    | exact resolve eq1887 eq1878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878 eq1887
  have eq2067 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq2065
       grind)
    | exact superpose eq2065 eq43
    | exact resolve eq43 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq2065
  have eq2071 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1443 eq2067
    | exact resolve eq2067 eq1443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2067
  have eq2072 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2071
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2071
    | exact resolve eq2071 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2071
  have eq2073 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1443 eq2072
    | exact resolve eq2072 eq1443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1443 eq2072
  have eq2100 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2073 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq2073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2073
  have eq2101 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2100
  have eq2340 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2041 eq2101
    | exact resolve eq2101 eq2041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2041 eq2101
  have eq2341 : False := by grind
  exact eq2341

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxx_pxy_pxy_x_pxy_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
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
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
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
  have eq175 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq176 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (k X0 X0)) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 X0
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (M.op (k (M.op X0 X1) (M.op X0 X1)) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 X1
       have i₂ := eq182 (M.op X0 X1)
       grind)
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq175 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq175
    | (have j0 := eq175 y
       grind)
    | exact resolve eq175 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : x = (M.op (k (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq188
       have i₂ := eq182 sF0
       grind)
    | exact superpose eq182 eq188
    | exact resolve eq188 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq199 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ y)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq205 : (σ x) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq199
       have i₂ := eq182 sF4
       grind)
    | exact superpose eq182 eq199
    | exact resolve eq199 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq218 : (σ x) = (M.op (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq179 sF2
       have i₂ := eq182 sF2
       grind)
    | exact superpose eq182 eq179
    | exact resolve eq179 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq639 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (k X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq187 (M.op (M.op X0 X1) (M.op X0 X2)) X1
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq187
    | exact resolve eq187 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq640 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (k x x) y) := by
    intro X0
    first
    | exact superpose eq175 eq187
    | exact resolve eq187 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq648 : (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) = (M.op (k (σ x) (σ x)) (σ x)) := by
    first
    | exact superpose eq218 eq187
    | exact resolve eq187 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649 : (k (M.op x y) (M.op x y)) = (M.op (k x x) y) := by
    first
    | exact superpose eq194 eq187
    | exact resolve eq187 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq650 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (k (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq205 eq187
    | exact resolve eq187 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq640 X0
       have i₂ := eq649
       grind)
    | exact superpose eq649 eq640
    | exact resolve eq640 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq704 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op x x) := by
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
  have eq705 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq747 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq748 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq747 X0 X1
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq747
    | (have j0 := eq747 X0 X1
       grind)
    | (have r₁ := eq747 X0 X0
       have r₂ := eq182 X0
       grind)
    | exact resolve eq747 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq789 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq705
       have i₂ := eq182 sF2
       grind)
    | exact superpose eq182 eq705
    | exact resolve eq705 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq790 : (M.op x y) = (k x y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq704
       have i₂ := eq182 x
       grind)
    | exact superpose eq182 eq704
    | exact resolve eq704 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq807 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X0 X0) ∨ (M.op X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq748 X0 X1
       have i₂ := eq182 X0
       grind)
    | exact superpose eq182 eq748
    | (have j0 := eq748 X0 X1
       grind)
    | exact resolve eq748 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq863 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (M.op y x) ∨ x = (k x y) := by
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
  have eq864 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq869 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq864
       have i₂ := eq182 sF2
       grind)
    | exact superpose eq182 eq864
    | exact resolve eq864 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq870 : (M.op x y) ≠ (k x x) ∨ (M.op x x) = (M.op y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq863
       have i₂ := eq182 x
       grind)
    | exact superpose eq182 eq863
    | exact resolve eq863 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq873 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq869
       have i₂ := eq182 sF2
       grind)
    | exact superpose eq182 eq869
    | exact resolve eq869 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq874 : (M.op x y) ≠ (k x x) ∨ (k x x) = (M.op y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq870
       have i₂ := eq182 x
       grind)
    | exact superpose eq182 eq870
    | exact resolve eq870 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq939 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq790
       grind)
    | exact superpose eq790 eq41
    | exact resolve eq41 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq940 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq939
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq939
    | exact resolve eq939 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939
  have eq942 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq20 eq940
    | exact resolve eq940 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq945 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq942 eq789
    | exact resolve eq789 eq942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq952 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq945
       have r₂ := eq27
       grind)
    | exact resolve eq945 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq1471 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq952 eq873
    | (have r₁ := eq873
       have r₂ := eq952
       grind)
    | exact resolve eq873 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq1472 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) := by grind
  clear eq1471
  have eq1473 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq942 eq1472
    | exact resolve eq1472 eq942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472
  have eq1475 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq1473 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq1473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq1484 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq1475
       have i₂ := eq182 sF2
       grind)
    | exact superpose eq182 eq1475
    | exact resolve eq1475 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475
  have eq1487 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq1484
       have r₂ := eq952
       grind)
    | exact resolve eq1484 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952 eq1484
  have eq1489 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq26 eq1487
    | exact resolve eq1487 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1487
  have eq1491 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq942 eq1489
    | exact resolve eq1489 eq942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942 eq1489
  have eq1492 : (M.op x y) = (k x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1491
       have r₂ := eq27
       grind)
    | exact resolve eq1491 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1491
  have eq1499 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1492
       grind)
    | exact superpose eq1492 eq40
    | exact resolve eq40 eq1492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1501 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x X0)) x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq185 x X0
       have i₂ := eq1492
       grind)
    | exact superpose eq1492 eq185
    | exact resolve eq185 eq1492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq1506 : x = (M.op (k (M.op x y) (M.op x y)) x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq663 eq1501
    | exact resolve eq1501 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663 eq1501
  have eq1507 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1499
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1499
    | exact resolve eq1499 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499
  have eq1511 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq1507
    | exact resolve eq1507 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1507
  have eq2176 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq874
       have i₂ := eq1492
       grind)
    | exact superpose eq1492 eq874
    | (have r₁ := eq874
       have r₂ := eq1492
       grind)
    | exact resolve eq874 eq1492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874 eq1492
  have eq2178 : (M.op x y) = (M.op y x) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2176
  have eq3146 : y = (M.op (k (M.op x y) (M.op x y)) x) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq187 y x
       have i₂ := eq2178
       grind)
    | exact superpose eq2178 eq187
    | exact resolve eq187 eq2178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2178
  have eq3149 : x = (k x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1506 eq3146
    | exact resolve eq3146 eq1506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1506 eq3146
  have eq3163 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq3149
       grind)
    | exact superpose eq3149 eq41
    | exact resolve eq41 eq3149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3149
  have eq3171 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3163
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3163
    | exact resolve eq3163 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3163
  have eq3177 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3171 eq789
    | exact resolve eq789 eq3171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3183 : (σ x) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3171 eq807
    | (have j0 := eq807 (σ x) (σ y)
       grind)
    | exact resolve eq807 eq3171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807 eq3171
  have eq3186 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) ≠ (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq3183
    | exact resolve eq3183 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3183
  have eq3192 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1511 eq3177
    | exact resolve eq3177 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3177
  have eq3194 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1511 eq3186
    | exact resolve eq3186 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511 eq3186
  have eq3198 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq3192
       have r₂ := eq27
       grind)
    | exact resolve eq3192 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3192
  have eq3200 : (σ x) ≠ (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq3194
       have r₂ := eq27
       grind)
    | exact resolve eq3194 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3194
  have eq3208 : (σ x) = (M.op (k (σ x) (σ x)) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3198 eq205
    | exact resolve eq205 eq3198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3263 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq650 eq3208
    | exact resolve eq3208 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3208
  have eq3268 : (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3198 eq3263
    | exact resolve eq3263 eq3198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3198 eq3263
  have eq3270 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq3268
       have r₂ := eq3200
       grind)
    | exact resolve eq3268 eq3200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3200 eq3268
  have eq3271 : (M.op x y) = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq3270 eq29
    | exact resolve eq29 eq3270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq3290 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq3271
    | exact resolve eq3271 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3271
  have eq3293 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq3290
       grind)
    | exact superpose eq3290 eq18
    | exact resolve eq18 eq3290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3301 : (k (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) y) ∨ x = y := by
    first
    | (have i₁ := eq649
       have i₂ := eq3290
       grind)
    | exact superpose eq3290 eq649
    | exact resolve eq649 eq3290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq3304 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq790
       have i₂ := eq3290
       grind)
    | exact superpose eq3290 eq790
    | exact resolve eq790 eq3290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3322 : x = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq194 eq3301
    | exact resolve eq3301 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq3301
  have eq3328 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq3290 eq3322
    | exact resolve eq3322 eq3290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3322
  have eq3334 : (M.op x y) ≠ (M.op (M.op x y) (M.op x y)) ∨ (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq3293 eq12
    | (have j0 := eq12 (M.op x y) y
       grind)
    | exact resolve eq12 eq3293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3293
  have eq3349 : (M.op x y) ≠ (k (M.op x y) (M.op x y)) ∨ (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq3334
       have i₂ := eq182 sF0
       grind)
    | exact superpose eq182 eq3334
    | exact resolve eq3334 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3334
  have eq3353 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) ∨ x = y := by
    first
    | (have r₁ := eq3349
       have r₂ := eq3304
       grind)
    | exact resolve eq3349 eq3304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3349
  have eq3355 : (k (M.op x y) (M.op x y)) = (M.op y (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq3353
       have i₂ := eq182 sF0
       grind)
    | exact superpose eq182 eq3353
    | exact resolve eq3353 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3353
  have eq3356 : (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq3304 eq3355
    | exact resolve eq3355 eq3304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3304 eq3355
  have eq3365 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq3328 eq42
    | exact resolve eq42 eq3328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq3376 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq20 eq3365
    | exact resolve eq3365 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3365
  have eq3381 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq3270 eq3376
    | exact resolve eq3376 eq3270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3376
  have eq3389 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ x = y := by
    first
    | exact superpose eq3381 eq218
    | exact resolve eq218 eq3381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq3390 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq3381 eq650
    | exact resolve eq650 eq3381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq3412 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq26 eq3390
    | exact resolve eq3390 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3390
  have eq3420 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3412 eq205
    | exact resolve eq205 eq3412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq3464 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3420 eq184
    | exact resolve eq184 eq3420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq3420
  have eq3474 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3412 eq3464
    | exact resolve eq3464 eq3412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3412 eq3464
  have eq4236 : (M.op (k (σ x) (σ x)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq3389 eq187
    | exact resolve eq187 eq3389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3389
  have eq4244 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq3381 eq4236
    | exact resolve eq4236 eq3381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4236
  have eq4254 : (k (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq4244
       have i₂ := eq182 sF2
       grind)
    | exact superpose eq182 eq4244
    | exact resolve eq4244 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4244
  have eq4264 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq3381 eq4254
    | exact resolve eq4254 eq3381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4254
  have eq4438 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = y := by
    first
    | exact superpose eq3474 eq28
    | exact resolve eq28 eq3474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3474
  have eq4453 : (M.op (σ x) (σ y)) = (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq4438
       have i₂ := eq639 sF2 sF4 sF4
       grind)
    | exact superpose eq639 eq4438
    | exact resolve eq4438 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639 eq4438
  have eq4463 : (M.op (σ x) (σ y)) = (M.op (k (σ x) (σ x)) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ x = y := by
    first
    | exact superpose eq648 eq4453
    | exact resolve eq4453 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648 eq4453
  have eq4471 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3381 eq4463
    | exact resolve eq4463 eq3381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4463
  have eq4477 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq4471
       have i₂ := eq182 sF2
       grind)
    | exact superpose eq182 eq4471
    | exact resolve eq4471 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4471
  have eq4482 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3381 eq4477
    | exact resolve eq4477 eq3381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3381 eq4477
  have eq4487 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq4264 eq4482
    | exact resolve eq4482 eq4264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4264 eq4482
  have eq7789 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq3356 eq41
    | exact resolve eq41 eq3356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq3356
  have eq7797 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq20 eq7789
    | exact resolve eq7789 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7789
  have eq7800 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq3270 eq7797
    | exact resolve eq7797 eq3270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7797
  have eq8054 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq7800 eq4487
    | exact resolve eq4487 eq7800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4487 eq7800
  have eq8067 : (M.op x y) = (M.op y (M.op x y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8054
  have eq8098 : y = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8067 eq187
    | exact resolve eq187 eq8067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq8067
  have eq8102 : y = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3328 eq8098
    | exact resolve eq8098 eq3328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8098
  have eq8106 : y = (k (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8102
       have i₂ := eq182 sF0
       grind)
    | exact superpose eq182 eq8102
    | exact resolve eq8102 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq8102
  have eq8109 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq3328 eq8106
    | exact resolve eq8106 eq3328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3328 eq8106
  have eq8112 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq8109 eq27
    | exact resolve eq27 eq8109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8109
  have eq8224 : y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq8112
       have r₂ := eq3270
       grind)
    | exact resolve eq8112 eq3270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3270 eq8112
  have eq8272 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq8224
  have eq8273 : x = y := by
    first
    | (have r₁ := eq8272
       have r₂ := eq3290
       grind)
    | exact resolve eq8272 eq3290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3290 eq8272
  have eq8287 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq8273
       grind)
    | exact superpose eq8273 eq24
    | exact resolve eq24 eq8273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq8294 : (M.op x y) = (k x x) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq790
       have i₂ := eq8273
       grind)
    | exact superpose eq8273 eq790
    | exact resolve eq790 eq8273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790 eq8273
  have eq8300 : (M.op x y) = (k x x) := by grind
  clear eq8294
  have eq8309 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq8287
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8287
    | exact resolve eq8287 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8287
  have eq8327 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq8309 eq789
    | exact resolve eq789 eq8309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789 eq8309
  have eq8340 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq8327
  have eq8371 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq8300
       grind)
    | exact superpose eq8300 eq40
    | exact resolve eq40 eq8300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq8300
  have eq8396 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq8371
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8371
    | exact resolve eq8371 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq8371
  have eq8403 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8340 eq8396
    | exact resolve eq8396 eq8340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8340 eq8396
  have eq8407 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq8403
    | exact resolve eq8403 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq8403
  have eq8409 : False := by grind
  exact eq8409

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxx_pxy_pxy_x_pxy_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq65 (σ X0)
       grind)
    | exact superpose eq65 eq10
    | exact resolve eq10 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq65 x
       grind)
    | exact superpose eq65 eq43
    | exact resolve eq43 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq71 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq68
       have i₂ := eq65 sF2
       grind)
    | exact superpose eq65 eq68
    | exact resolve eq68 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq72 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq67
    | exact resolve eq67 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq76 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ x = (k x y) := by
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
  have eq77 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq93 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq91
       have i₂ := eq65 sF3
       grind)
    | exact superpose eq65 eq91
    | exact resolve eq91 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq95 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq93
       have i₂ := eq65 y
       grind)
    | exact superpose eq65 eq93
    | exact resolve eq93 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq107 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq84
    | (have j0 := eq84 (σ X0) (σ X1)
       grind)
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq84 x y
       grind)
    | exact superpose eq84 eq44
    | (have j1 := eq84 x y
       grind)
    | exact resolve eq44 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq120
    | exact resolve eq120 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq123 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq122
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq122
    | exact resolve eq122 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq135 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq146 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq143
       have i₂ := eq65 sF1
       grind)
    | exact superpose eq65 eq143
    | exact resolve eq143 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq148 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq146
       have i₂ := eq65 sF0
       grind)
    | exact superpose eq65 eq146
    | exact resolve eq146 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq146
  have eq234 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq50
  have eq237 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq243 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq237 eq14
    | exact resolve eq14 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq618 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X4)) X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq629 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq641 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X1 X2 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X2)) (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X2)) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X2)) X3) X1
       have i₂ := eq52 X0 (M.op X0 X1) X2 X3
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq764 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq123 eq84
    | (have j0 := eq84 (σ x) (σ y)
       grind)
    | exact resolve eq84 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq765 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq764
    | exact resolve eq764 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq768 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq765
       have r₂ := eq27
       grind)
    | exact resolve eq765 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq770 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq768
    | exact resolve eq768 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq772 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq770 eq77
    | (have r₁ := eq77
       have r₂ := eq770
       grind)
    | exact resolve eq77 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq784 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq770 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | exact resolve eq13 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq785 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq772
  have eq786 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq107 X0 X1
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq107
    | (have j0 := eq107 X0 X1
       grind)
    | exact resolve eq107 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq107
  have eq850 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) (σ X1) X2
       have i₂ := eq786 X0 X1
       grind)
    | exact superpose eq786 eq14
    | (have j1 := eq786 X0 X1
       grind)
    | exact resolve eq14 eq786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq859 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq786 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq962 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq641
    | (have j0 := eq641 (σ x) (σ y) X0
       grind)
    | exact resolve eq641 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq991 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq641 X0 X1 x
       grind)
    | exact superpose eq641 eq14
    | exact resolve eq14 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3840 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) X0))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq239 X0 (M.op sF4 x)
       have i₂ := eq641 sF4 (M.op sF2 X0) x
       grind)
    | exact superpose eq641 eq239
    | exact resolve eq239 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq7103 : ∀ X0 : G, (k (σ (M.op x y)) X0) ≠ (σ (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (τ X0))) := by
    intro X0
    first
    | exact superpose eq135 eq859
    | (have j0 := eq859 (M.op x y) (τ X0)
       grind)
    | exact resolve eq859 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq859
  have eq7127 : ∀ X0 : G, (k (σ (M.op x y)) X0) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (τ X0))) := by
    intro X0
    first
    | exact superpose eq148 eq7103
    | (have j0 := eq7103 X0
       grind)
    | exact resolve eq7103 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7103
  have eq7156 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ (k (σ (M.op x y)) X0) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq7127 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq7127
    | (have j0 := eq7127 X0
       grind)
    | exact resolve eq7127 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7127
  have eq7180 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ (k (σ (M.op x y)) X0) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq7156
    | (have j0 := eq7156 X0
       grind)
    | exact resolve eq7156 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7156
  have eq7200 : ∀ X0 : G, (k (σ (M.op x y)) X0) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq148 eq7180
    | (have j0 := eq7180 X0
       grind)
    | exact resolve eq7180 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq7180
  have eq7510 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X1)) (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X3)) = X0 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq642 X0 X1 x X3
       have i₂ := eq641 X0 (M.op X0 X1) x
       grind)
    | exact superpose eq641 eq642
    | exact resolve eq642 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq7511 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X0) X3)) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq7510 x x X3
       have i₂ := eq641 x x x
       grind)
    | exact superpose eq641 eq7510
    | exact resolve eq7510 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7510
  have eq7595 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq641 (M.op (M.op X0 X0) X0) X1 (M.op (M.op (M.op X0 X0) X0) x)
       have i₂ := eq7511 X0 x
       grind)
    | exact superpose eq7511 eq641
    | exact resolve eq641 eq7511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7596 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7595 X0 X1
       have i₂ := eq641 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq641 eq7595
    | exact resolve eq7595 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7595
  have eq7604 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq7596 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq7596
    | exact resolve eq7596 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7596
  have eq8031 : ∀ X0 : G, (σ x) = (M.op (M.op (k (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq850 x y X0
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq850
    | (have j0 := eq850 x y x
       grind)
    | exact resolve eq850 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq8159 : ∀ X0 : G, (σ x) = (M.op (M.op (k (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq8031 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8031
    | (have j0 := eq8031 X0
       grind)
    | exact resolve eq8031 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8031
  have eq8206 : ∀ X0 : G, (σ x) = (M.op (M.op (k (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq8159 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8159
    | (have j0 := eq8159 X0
       grind)
    | exact resolve eq8159 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8159
  have eq8240 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (M.op (k (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq8206 X0
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq8206
    | (have j0 := eq8206 X0
       grind)
    | exact resolve eq8206 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8206
  have eq8272 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (M.op (k (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq8240 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8240
    | (have j0 := eq8240 X0
       grind)
    | exact resolve eq8240 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8240
  have eq8300 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (M.op (k (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq8272 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8272
    | (have j0 := eq8272 X0
       grind)
    | exact resolve eq8272 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8272
  have eq8310 : ∀ X0 : G, (σ x) = (M.op (M.op (k (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq8300
    | (have j0 := eq8300 X0
       grind)
    | exact resolve eq8300 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8300
  have eq11149 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X0 X0) X1) X3)) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 (M.op (M.op (M.op X0 X0) X1) X3)) X4)) X1) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq618 X0 X1 x X3 X4
       have i₂ := eq641 X0 X1 x
       grind)
    | exact superpose eq641 eq618
    | exact resolve eq618 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq11493 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) X1) X2))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11149 X0 X1 X2 (M.op X0 x)
       have i₂ := eq641 X0 (M.op (M.op (M.op X0 X0) X1) X2) x
       grind)
    | exact superpose eq641 eq11149
    | exact resolve eq11149 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11149
  have eq11506 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11493 X0 X1 X2
       have i₂ := eq14 (M.op X0 X0) X1 (M.op (M.op (M.op X0 X0) X1) X2)
       grind)
    | exact superpose eq14 eq11493
    | exact resolve eq11493 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11493
  have eq11551 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) X3) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq629 X0 X1 x X3 X4
       have i₂ := eq641 X0 X1 x
       grind)
    | exact superpose eq641 eq629
    | exact resolve eq629 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq11798 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11551 X1 (M.op X1 X2) X1 x
       have i₂ := eq14 X1 X1 X2
       grind)
    | exact superpose eq14 eq11551
    | exact resolve eq11551 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11844 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X2)) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11551 X1 X1 (M.op (M.op X1 X1) X2) x
       have i₂ := eq14 (M.op X1 X1) X1 X2
       grind)
    | exact superpose eq14 eq11551
    | exact resolve eq11551 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11551
  have eq11912 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11844 X0 X1 x
       have i₂ := eq641 (M.op X0 X0) X0 x
       grind)
    | exact superpose eq641 eq11844
    | exact resolve eq11844 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11844
  have eq11951 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11798 X0 X1 x
       have i₂ := eq641 (M.op X0 X0) (M.op X0 X1) x
       grind)
    | exact superpose eq641 eq11798
    | exact resolve eq11798 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11798
  have eq11982 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11912 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq11912
    | exact resolve eq11912 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11912
  have eq12020 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11951 X0 X1
       have i₂ := eq641 X0 X0 X0
       grind)
    | exact superpose eq641 eq11951
    | exact resolve eq11951 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11951
  have eq73019 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12020 X0 X1
       have i₂ := eq7604 X0 (M.op X0 X1)
       grind)
    | exact superpose eq7604 eq12020
    | exact resolve eq12020 eq7604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7604 eq12020
  have eq95653 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq243 eq3840
    | exact resolve eq3840 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243 eq3840
  have eq136059 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq785 eq784
    | (have j0 := eq784 (σ y)
       grind)
    | (have r₁ := eq784 (σ y)
       have r₂ := eq785
       grind)
    | exact resolve eq784 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784 eq785
  have eq136064 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq136059
  have eq136065 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq136064
  have eq136087 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq136065
    | exact resolve eq136065 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136065
  have eq136410 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq123 eq136087
    | exact resolve eq136087 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136415 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq136087 eq123
    | exact resolve eq123 eq136087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq136087
  have eq136430 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq136415
  have eq136431 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq136410
  have eq136434 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq136430
       have r₂ := eq27
       grind)
    | exact resolve eq136430 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136430
  have eq136435 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq136431
       have r₂ := eq27
       grind)
    | exact resolve eq136431 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136431
  have eq136438 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq136435
       grind)
    | exact superpose eq136435 eq71
    | exact resolve eq71 eq136435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136435
  have eq136559 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq136438
    | exact resolve eq136438 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136438
  have eq136740 : (σ x) = (M.op (M.op (k (σ x) (σ y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq136559 eq8310
    | exact resolve eq8310 eq136559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8310
  have eq136805 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (M.op (σ (M.op x y)) X0) X1)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq136559 eq11506
    | exact resolve eq11506 eq136559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11506
  have eq136837 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq136559 eq73019
    | exact resolve eq73019 eq136559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136846 : (σ x) = (M.op (M.op (k (σ x) (σ y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq136740
       have r₂ := eq27
       grind)
    | exact resolve eq136740 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136740
  have eq137256 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq136837 eq73019
    | exact resolve eq73019 eq136837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136837
  have eq137272 : (τ (σ x)) = (k x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq136434 eq59
    | exact resolve eq59 eq136434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq136434
  have eq137297 : (M.op x y) = (M.op x x) ∨ x = (k x y) := by
    first
    | exact superpose eq28 eq137272
    | exact resolve eq137272 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137272
  have eq139125 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq137297
       grind)
    | exact superpose eq137297 eq76
    | (have r₁ := eq76
       have r₂ := eq137297
       grind)
    | exact resolve eq76 eq137297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq137297
  have eq139211 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = (k x y) := by grind
  clear eq139125
  have eq139212 : (M.op x y) = (M.op y y) ∨ x = (k x y) := by grind
  clear eq139211
  have eq140945 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq139212
       grind)
    | exact superpose eq139212 eq95
    | exact resolve eq95 eq139212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq140973 : ∀ X0 : G, y = (M.op (M.op (M.op x y) y) (M.op (M.op (M.op x y) y) X0)) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq7511 y x
       have i₂ := eq139212
       grind)
    | exact superpose eq139212 eq7511
    | exact resolve eq7511 eq139212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7511 eq139212
  have eq141013 : y = (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq140973 x
       have i₂ := eq73019 (M.op sF0 y) x
       grind)
    | exact superpose eq73019 eq140973
    | exact resolve eq140973 eq73019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73019 eq140973
  have eq141030 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq20 eq140945
    | exact resolve eq140945 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq140945
  have eq141033 : y = (M.op (M.op (M.op x y) (M.op x y)) y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq141013
       have i₂ := eq641 sF0 y y
       grind)
    | exact superpose eq641 eq141013
    | exact resolve eq141013 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641 eq141013
  have eq141044 : x = (k x y) ∨ x = y := by
    first
    | exact superpose eq234 eq141033
    | exact resolve eq141033 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141033
  have eq141047 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq141044
       grind)
    | exact superpose eq141044 eq44
    | exact resolve eq44 eq141044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141044
  have eq141092 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq141047
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq141047
    | exact resolve eq141047 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141047
  have eq141603 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ (M.op x y)))) = (M.op (M.op (σ x) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq137256 eq962
    | exact resolve eq962 eq137256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq141691 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ (M.op x y))) X0) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq137256 eq991
    | exact resolve eq991 eq137256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137256
  have eq141742 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq95653 eq141603
    | exact resolve eq141603 eq95653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95653 eq141603
  have eq142178 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x y)) X0) X0) ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq141030 eq991
    | exact resolve eq991 eq141030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991 eq141030
  have eq179252 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by
    first
    | exact superpose eq142178 eq136805
    | exact resolve eq136805 eq142178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136805 eq142178
  have eq179337 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by
    first
    | exact superpose eq26 eq179252
    | exact resolve eq179252 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179252
  have eq179346 : x = (k x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq179337
       have r₂ := eq27
       grind)
    | exact resolve eq179337 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179337
  have eq179465 : (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq179346
       grind)
    | exact superpose eq179346 eq44
    | exact resolve eq44 eq179346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq179346
  have eq179518 : (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq179465
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq179465
    | exact resolve eq179465 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179465
  have eq179644 : (σ x) = (M.op (M.op (σ x) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq179518 eq136846
    | exact resolve eq136846 eq179518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136846 eq179518
  have eq179666 : (σ x) = (M.op (M.op (σ x) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq179644
  have eq179694 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq179666 eq141742
    | exact resolve eq141742 eq179666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141742
  have eq179695 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq179666 eq141691
    | exact resolve eq141691 eq179666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141691 eq179666
  have eq179720 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq179695
  have eq179721 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq179694
  have eq179737 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq179720
    | exact resolve eq179720 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179720
  have eq181203 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq179737 eq179721
    | exact resolve eq179721 eq179737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179721 eq179737
  have eq181433 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq181203
  have eq183330 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq181433 eq136559
    | exact resolve eq136559 eq181433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136559 eq181433
  have eq183522 : (σ (M.op x y)) = (σ x) := by grind
  clear eq183330
  have eq184120 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq183522 eq26
    | exact resolve eq26 eq183522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq184121 : x = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq183522 eq28
    | exact resolve eq28 eq183522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq184573 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq183522 eq141092
    | exact resolve eq141092 eq183522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141092
  have eq184659 : x = (M.op x y) := by
    first
    | exact superpose eq30 eq184121
    | exact resolve eq184121 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq184121
  have eq184729 : x = (M.op (M.op x x) y) := by
    first
    | exact superpose eq184659 eq234
    | exact resolve eq234 eq184659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq184659
  have eq187218 : ∀ X0 : G, (M.op x x) = (M.op (M.op x (M.op (M.op x x) X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op x x) y X0
       have i₂ := eq184729
       grind)
    | exact superpose eq184729 eq14
    | exact resolve eq14 eq184729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187244 : (M.op x x) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq187218 x
       have i₂ := eq11982 x x
       grind)
    | exact superpose eq11982 eq187218
    | exact resolve eq187218 eq11982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11982 eq187218
  have eq187285 : x = (M.op x x) := by
    first
    | (have i₁ := eq187244
       have i₂ := eq184729
       grind)
    | exact superpose eq184729 eq187244
    | exact resolve eq187244 eq184729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184729 eq187244
  have eq187331 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq187285
       grind)
    | exact superpose eq187285 eq71
    | exact resolve eq71 eq187285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq187285
  have eq187561 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq183522 eq187331
    | exact resolve eq187331 eq183522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187331
  have eq187612 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq187561
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq187561
    | exact resolve eq187561 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187561
  have eq187647 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq183522 eq187612
    | exact resolve eq187612 eq183522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187612
  have eq197768 : (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq184573 eq7200
    | (have j0 := eq7200 (σ y)
       grind)
    | exact resolve eq7200 eq184573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7200 eq184573
  have eq197788 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq197768
       have r₂ := eq187647
       grind)
    | exact resolve eq197768 eq187647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197768
  have eq197804 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq184120 eq197788
    | exact resolve eq197788 eq184120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197788
  have eq197819 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq187647 eq197804
    | exact resolve eq197804 eq187647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197804
  have eq197835 : x = y := by
    first
    | (have r₁ := eq197819
       have r₂ := eq27
       grind)
    | exact resolve eq197819 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197819
  have eq197851 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq197835
       grind)
    | exact superpose eq197835 eq24
    | exact resolve eq24 eq197835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq197835
  have eq198183 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq197851
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq197851
    | exact resolve eq197851 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq197851
  have eq198331 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq183522 eq198183
    | exact resolve eq198183 eq183522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183522 eq198183
  have eq199959 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq198331 eq184120
    | exact resolve eq184120 eq198331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184120 eq198331
  have eq199965 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq187647 eq199959
    | exact resolve eq199959 eq187647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187647 eq199959
  have eq200171 : False := by grind
  exact eq200171
