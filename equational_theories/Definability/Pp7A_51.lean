import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pyx_pxy_x_Equation3008 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) Law3008 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq14 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq93 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq68
       grind)
    | exact superpose eq68 eq16
    | exact resolve eq16 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq103 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq103 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq103 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq103 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq116 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq93
       have i₂ := eq104 sF3
       grind)
    | exact superpose eq104 eq93
    | exact resolve eq93 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq117 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq116
       have i₂ := eq104 y
       grind)
    | exact superpose eq104 eq116
    | exact resolve eq116 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq126 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq127 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq128 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq127
       have i₂ := eq104 sF1
       grind)
    | exact superpose eq104 eq127
    | exact resolve eq127 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq131 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq128
       have i₂ := eq104 sF0
       grind)
    | exact superpose eq104 eq128
    | exact resolve eq128 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq128
  have eq366 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq51 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X2 X2)) (M.op X1 X1) X1
       have i₂ := eq51 (M.op X1 X1) X0 X2
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X1) = (M.op X0 (M.op (M.op (M.op X4 X4) (M.op X5 X5)) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq50 (M.op X1 X0) X4 X5 (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X1)
       have i₂ := eq50 X1 X2 X3 X0
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq439 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 X1 x (M.op X0 X0) X2
       have i₂ := eq51 x (M.op X0 X0) X0
       grind)
    | exact superpose eq51 eq50
    | exact resolve eq50 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1001 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq366 (M.op X0 X0) x X1
       have i₂ := eq51 x (M.op X0 X0) X0
       grind)
    | exact superpose eq51 eq366
    | exact resolve eq366 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1014 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) ≠ (M.op (M.op X0 X0) (M.op X1 X1)) ∨ (M.op X2 X2) = X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X2
       have i₂ := eq366 X1 X0 X3
       grind)
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq366 X0 X0 X2
       grind)
    | exact superpose eq366 eq12
    | (have j0 := eq12 X3 X2
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X2
       have r₂ := eq366 X0 X0 X2
       grind)
    | (have r₁ := eq12 X2 (M.op X0 X0)
       have r₂ := eq366 X0 X0 X2
       grind)
    | exact resolve eq12 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1072 : ∀ X2 X3 : G, (k X3 X2) = (M.op X3 X2) ∨ (M.op X2 X2) = X2 := by
    intro X2 X3
    first
    | (have j0 := eq1014 x x X2 X3
       grind)
    | (have r₁ := eq1014 x x X2 X3
       have r₂ := eq366 x x X2
       grind)
    | (have r₁ := eq1014 x x (M.op x x) X3
       have r₂ := eq366 x x (M.op x x)
       grind)
    | exact resolve eq1014 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq2639 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) (M.op X1 X1)) ∨ (M.op (M.op X0 X0) X2) = (k X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 X0)
       have i₂ := eq371 (M.op X0 X0) X0 X1
       grind)
    | (have i₁ := eq13 X2 (M.op X0 X0)
       have i₂ := eq371 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq371 eq13
    | (have j0 := eq13 X2 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq2695 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = (k X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have j0 := eq2639 X0 x X2
       grind)
    | (have r₁ := eq2639 x X0 X2
       have r₂ := eq366 X0 x x
       grind)
    | (have r₁ := eq2639 (M.op X0 X0) (M.op X0 X0) X2
       have r₂ := eq366 X0 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq2639 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq2639
  have eq3104 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 X0) x)) := by
    intro X0
    first
    | (have i₁ := eq439 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq439
    | (have j0 := eq439 X0 x y
       grind)
    | exact resolve eq439 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25891 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1072 y x
       grind)
    | exact superpose eq1072 eq44
    | (have j1 := eq1072 y x
       grind)
    | exact resolve eq44 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq25953 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq25891
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25891
    | exact resolve eq25891 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq25891
  have eq25993 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq25953
    | exact resolve eq25953 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq25953
  have eq26002 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq25993 eq1072
    | (have j0 := eq1072 (σ y) x
       grind)
    | exact resolve eq1072 eq25993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072 eq25993
  have eq26011 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq26002
    | exact resolve eq26002 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26002
  have eq26022 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq26011
       have r₂ := eq27
       grind)
    | exact resolve eq26011 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26011
  have eq26034 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26022 eq117
    | exact resolve eq117 eq26022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq26022
  have eq26189 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq26034
    | exact resolve eq26034 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq26034
  have eq26190 : y = (M.op y y) := by grind
  clear eq26189
  have eq26196 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq26190
       have i₂ := eq1001 X0 y
       grind)
    | (have i₁ := eq26190
       have i₂ := eq1001 y X0
       grind)
    | exact superpose eq1001 eq26190
    | exact resolve eq26190 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq26302 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq2695 y x
       have i₂ := eq26190
       grind)
    | exact superpose eq26190 eq2695
    | exact resolve eq2695 eq26190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2695
  have eq26307 : y = (M.op (M.op x y) (M.op y x)) := by
    first
    | (have i₁ := eq3104 y
       have i₂ := eq26190
       grind)
    | exact superpose eq26190 eq3104
    | exact resolve eq3104 eq26190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3104
  have eq26575 : ∀ X0 X1 : G, (M.op y (M.op (M.op X1 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq439 X1 X0 X0
       have i₂ := eq26196 X0
       grind)
    | exact superpose eq26196 eq439
    | exact resolve eq439 eq26196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq26638 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 (M.op X1 X1)) X0 X1
       have i₂ := eq26196 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq26196 eq14
    | exact resolve eq14 eq26196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26667 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq131
       have i₂ := eq26196 sF0
       grind)
    | exact superpose eq26196 eq131
    | exact resolve eq131 eq26196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq26675 : y = (σ y) := by
    first
    | (have i₁ := eq26667
       have i₂ := eq26196 sF1
       grind)
    | exact superpose eq26196 eq26667
    | exact resolve eq26667 eq26196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26667
  have eq26703 : ∀ X0 : G, (M.op y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq26638 X0 x
       have i₂ := eq26196 x
       grind)
    | exact superpose eq26196 eq26638
    | exact resolve eq26638 eq26196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26638
  have eq26748 : ∀ X0 : G, (M.op y (M.op y X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq26575 X0 x
       have i₂ := eq26196 x
       grind)
    | exact superpose eq26196 eq26575
    | exact resolve eq26575 eq26196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26575
  have eq26901 : y = (σ y) := by
    first
    | (have i₁ := eq26675
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26675
    | exact resolve eq26675 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq26675
  have eq27127 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq26901 eq26
    | exact resolve eq26 eq26901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq31751 : (k (σ (M.op x y)) (σ y)) = (σ (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq126
       have i₂ := eq26302 sF0
       grind)
    | exact superpose eq26302 eq126
    | exact resolve eq126 eq26302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq31790 : (σ (M.op y (M.op x y))) = (k (σ (M.op x y)) y) := by
    first
    | exact superpose eq26901 eq31751
    | exact resolve eq31751 eq26901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26901 eq31751
  have eq31828 : (σ (M.op y (M.op x y))) = (M.op y (σ (M.op x y))) := by
    first
    | (have i₁ := eq31790
       have i₂ := eq26302 sF1
       grind)
    | exact superpose eq26302 eq31790
    | exact resolve eq31790 eq26302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26302 eq31790
  have eq31876 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op x y)) = (M.op (M.op y x) (M.op (M.op (M.op X2 X2) (M.op X3 X3)) y)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq26307 eq428
    | exact resolve eq428 eq26307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428 eq26307
  have eq31885 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq31876 X0 X1 x x
       have i₂ := eq50 y x x x
       grind)
    | exact superpose eq50 eq31876
    | exact resolve eq31876 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq31876
  have eq31888 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq31885 X0 x
       have i₂ := eq26196 x
       grind)
    | exact superpose eq26196 eq31885
    | exact resolve eq31885 eq26196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31885
  have eq31890 : x = (M.op (M.op y y) (M.op x y)) := by
    first
    | (have i₁ := eq31888 x
       have i₂ := eq26196 x
       grind)
    | exact superpose eq26196 eq31888
    | exact resolve eq31888 eq26196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26196 eq31888
  have eq31891 : x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq31890
       have i₂ := eq26190
       grind)
    | exact superpose eq26190 eq31890
    | exact resolve eq31890 eq26190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26190 eq31890
  have eq32137 : (M.op (σ x) (σ y)) = (M.op y (σ x)) := by
    first
    | exact superpose eq27127 eq26703
    | exact resolve eq26703 eq27127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26703 eq27127
  have eq33046 : (σ x) = (M.op y (σ (M.op x y))) := by
    first
    | exact superpose eq31891 eq31828
    | exact resolve eq31828 eq31891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31828 eq31891
  have eq33047 : (σ x) = (M.op y (σ (M.op x y))) := by
    first
    | (have i₁ := eq33046
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq33046
    | exact resolve eq33046 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq33046
  have eq33048 : (σ (M.op x y)) = (M.op y (σ x)) := by
    first
    | exact superpose eq33047 eq26748
    | exact resolve eq26748 eq33047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26748 eq33047
  have eq33061 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32137 eq33048
    | exact resolve eq33048 eq32137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32137 eq33048
  have eq33066 : False := by grind
  exact eq33066

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pxx_pxy_Equation3008 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3008 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq14 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (σ (k y (k x x))) = (k (σ y) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq36 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq36
    | exact resolve eq36 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq103 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq103 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq103 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq103 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq106 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq104 (σ X0)
       grind)
    | exact superpose eq104 eq10
    | exact resolve eq10 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq104 sF2
       grind)
    | exact superpose eq104 eq49
    | exact resolve eq49 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq110 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq109
       have i₂ := eq104 x
       grind)
    | exact superpose eq104 eq109
    | exact resolve eq109 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq113 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq106 X0
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq106
    | exact resolve eq106 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
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
  have eq132 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq129
       have i₂ := eq104 sF1
       grind)
    | exact superpose eq104 eq129
    | exact resolve eq129 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq135 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq132
       have i₂ := eq104 sF0
       grind)
    | exact superpose eq104 eq132
    | exact resolve eq132 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq157 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq135 eq16
    | exact resolve eq16 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq104 (τ X0)
       grind)
    | exact superpose eq104 eq34
    | exact resolve eq34 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
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
  clear eq34
  have eq269 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq258 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq258
    | exact resolve eq258 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq271 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq269 X0
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq269
    | exact resolve eq269 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq367 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq51 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       have i₂ := eq14 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X2 X2)) (M.op X1 X1) X1
       have i₂ := eq51 (M.op X1 X1) X0 X2
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq51 X1 (M.op X0 X0) X0
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq50
    | (have j0 := eq50 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq426 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X1 (M.op X2 X2)) X0))) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq50 (M.op (M.op X1 (M.op X2 X2)) X0) X3 X4 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X1) = (M.op X0 (M.op (M.op (M.op X4 X4) (M.op X5 X5)) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq50 (M.op X1 X0) X4 X5 (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X1)
       have i₂ := eq50 X1 X2 X3 X0
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 X1 x (M.op X0 X0) X2
       have i₂ := eq51 x (M.op X0 X0) X0
       grind)
    | exact superpose eq51 eq50
    | exact resolve eq50 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 (M.op (M.op X0 X0) (M.op X1 X1))) X3) X2) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X2 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1)))
       have i₂ := eq50 (M.op (M.op X0 X0) (M.op X1 X1)) X0 X1 (M.op (M.op X0 X0) (M.op X1 X1))
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq621 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq271 X0
       grind)
    | exact superpose eq271 eq16
    | exact resolve eq16 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : ∀ X0 : G, (σ (k y (M.op (τ X0) (τ X0)))) = (k (σ y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 (M.op (τ X0) (τ X0))
       have i₂ := eq271 X0
       grind)
    | exact superpose eq271 eq36
    | exact resolve eq36 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq711 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 X1
       have i₂ := eq113 X1
       grind)
    | exact superpose eq113 eq70
    | (have j0 := eq70 X0 X1
       grind)
    | exact resolve eq70 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq712 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq711 X0 X1
       have i₂ := eq113 X1
       grind)
    | exact superpose eq113 eq711
    | (have j0 := eq711 X0 X1
       grind)
    | exact resolve eq711 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq807 : ∀ X0 X1 X2 X3 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (σ X0))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 (σ X0) X2 X3 (σ X1)
       have i₂ := eq712 X0 X1
       grind)
    | exact superpose eq712 eq50
    | (have j1 := eq712 X0 X1
       grind)
    | exact resolve eq50 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq712
  have eq912 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq367 (M.op X0 X0) x X1
       have i₂ := eq51 x (M.op X0 X0) X0
       grind)
    | exact superpose eq51 eq367
    | exact resolve eq367 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq925 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3) (M.op X2 X2)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op X2 X2) X2
       have i₂ := eq367 X1 X0 (M.op X2 X2)
       grind)
    | (have i₁ := eq14 X0 (M.op X1 X1) X0
       have i₂ := eq367 X0 X1 X2
       grind)
    | exact superpose eq367 eq14
    | exact resolve eq14 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq969 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq912 X1 (σ X0)
       have i₂ := eq113 X0
       grind)
    | exact superpose eq113 eq912
    | exact resolve eq912 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1095 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X0) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X1 (M.op X0 (M.op X2 X2)) x
       have i₂ := eq369 X0 X2 x
       grind)
    | exact superpose eq369 eq51
    | exact resolve eq51 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1096 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op X1 X1))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X3 (M.op X0 (M.op X1 X1)) x
       have i₂ := eq369 X0 X1 x
       grind)
    | exact superpose eq369 eq14
    | exact resolve eq14 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq1188 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) (M.op X1 X1)) ∨ (M.op (M.op X0 X0) X2) = (k X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 X0)
       have i₂ := eq370 (M.op X0 X0) X0 X1
       grind)
    | (have i₁ := eq13 X2 (M.op X0 X0)
       have i₂ := eq370 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq370 eq13
    | (have j0 := eq13 X2 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq1218 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = (k X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have j0 := eq1188 X0 x X2
       grind)
    | (have r₁ := eq1188 x X0 X2
       have r₂ := eq367 X0 x x
       grind)
    | (have r₁ := eq1188 (M.op X0 X0) (M.op X0 X0) X2
       have r₂ := eq367 X0 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq1188 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1239 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq969 X1 (τ X0)
       have i₂ := eq621 X0
       grind)
    | exact superpose eq621 eq969
    | exact resolve eq969 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1501 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X2 X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq433 X2 X1 X1
       have i₂ := eq912 X0 X1
       grind)
    | (have i₁ := eq433 X2 X1 X1
       have i₂ := eq912 X1 X0
       grind)
    | exact superpose eq912 eq433
    | exact resolve eq433 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq1503 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X3 X3) X2)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq433 X3 X2 X2
       have i₂ := eq367 X1 X0 X2
       grind)
    | (have i₁ := eq433 X0 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq367 X0 X1 X2
       grind)
    | exact superpose eq367 eq433
    | exact resolve eq433 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq1510 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X1) = (M.op X0 (M.op (M.op X3 X3) (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq433 X3 (M.op X1 X0) (M.op (M.op X2 X2) X1)
       have i₂ := eq433 X2 X1 X0
       grind)
    | exact superpose eq433 eq433
    | exact resolve eq433 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1516 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 X0) x)) := by
    intro X0
    first
    | (have i₁ := eq433 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq433
    | (have j0 := eq433 X0 x y
       grind)
    | exact resolve eq433 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2228 : ∀ X0 X2 : G, (τ (M.op X2 X2)) = (σ (σ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq1239 X2 x
       have i₂ := eq969 X0 x
       grind)
    | exact superpose eq969 eq1239
    | exact resolve eq1239 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3239 : ∀ X0 X1 : G, (σ (k (k (τ X0) X1) (M.op (M.op x y) (M.op x y)))) = (k (k X0 (σ X1)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq135 eq260
    | exact resolve eq260 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq4595 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op x (M.op (M.op X0 X0) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1516 (M.op x (M.op (M.op X0 X0) (M.op X1 X1)))
       have i₂ := eq446 X0 X1 x (M.op x (M.op (M.op X0 X0) (M.op X1 X1)))
       grind)
    | exact superpose eq446 eq1516
    | exact resolve eq1516 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq1516
  have eq5580 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op (M.op X0 (M.op X4 X4)) X1)) = (M.op X0 (M.op (M.op X5 X5) X1)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq433 X5 X1 (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op (M.op X0 (M.op X4 X4)) X1))
       have i₂ := eq426 X1 X0 X4 X2 X3
       grind)
    | exact superpose eq426 eq433
    | exact resolve eq433 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq6838 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (M.op X3 X0))) (M.op X5 X5)) = X3 := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq372 (M.op x x) X5 X3
       have i₂ := eq428 X0 X3 x x X1 X2
       grind)
    | exact superpose eq428 eq372
    | exact resolve eq372 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq8304 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1218 (σ X0) x
       have i₂ := eq113 X0
       grind)
    | exact superpose eq113 eq1218
    | exact resolve eq1218 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq9500 : ∀ X0 X1 X2 X3 : G, (σ X1) = (M.op (σ (M.op X0 X1)) (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (σ X0))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq807 X0 X1 X2 X3
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq807
    | (have j0 := eq807 X0 X1 X2 X3
       have j1 := eq11 X0 X1
       grind)
    | exact resolve eq807 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq11751 : (σ (k y (k x x))) = (k (σ y) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq64
       have i₂ := eq104 sF2
       grind)
    | exact superpose eq104 eq64
    | exact resolve eq64 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq11752 : (σ (k y (k x x))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq11751
       have i₂ := eq1218 sF2 sF3
       grind)
    | exact superpose eq1218 eq11751
    | exact resolve eq11751 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11751
  have eq11753 : (σ (k y (M.op x x))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq11752
       have i₂ := eq104 x
       grind)
    | exact superpose eq104 eq11752
    | exact resolve eq11752 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq11752
  have eq11754 : (M.op (M.op (σ x) (σ x)) (σ y)) = (σ (M.op (M.op x x) y)) := by
    first
    | (have i₁ := eq11753
       have i₂ := eq1218 x y
       grind)
    | exact superpose eq1218 eq11753
    | exact resolve eq11753 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11753
  have eq22038 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (σ y)) = (σ (M.op y (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11754
       have i₂ := eq1095 y x X0
       grind)
    | exact superpose eq1095 eq11754
    | exact resolve eq11754 eq1095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22041 : (M.op (M.op x x) y) = (τ (M.op (M.op (σ x) (σ x)) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op (M.op x x) y)
       have i₂ := eq11754
       grind)
    | exact superpose eq11754 eq16
    | exact resolve eq16 eq11754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11754
  have eq44248 : ∀ X0 : G, (σ (k y (M.op (τ X0) (τ X0)))) = (M.op (M.op X0 X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq623 X0
       have i₂ := eq1218 X0 sF3
       grind)
    | exact superpose eq1218 eq623
    | exact resolve eq623 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq44249 : ∀ X0 : G, (M.op (M.op X0 X0) (σ y)) = (σ (M.op (M.op (τ X0) (τ X0)) y)) := by
    intro X0
    first
    | (have i₁ := eq44248 X0
       have i₂ := eq1218 (τ X0) y
       grind)
    | exact superpose eq1218 eq44248
    | exact resolve eq44248 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44248
  have eq44250 : ∀ X0 : G, (M.op (M.op X0 X0) (σ y)) = (σ (M.op (τ (M.op X0 X0)) y)) := by
    intro X0
    first
    | (have i₁ := eq44249 X0
       have i₂ := eq621 X0
       grind)
    | exact superpose eq621 eq44249
    | exact resolve eq44249 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621 eq44249
  have eq65996 : ∀ X0 : G, (M.op (M.op x x) y) = (τ (M.op (σ y) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq22041
       have i₂ := eq1095 sF3 sF2 x
       grind)
    | exact superpose eq1095 eq22041
    | exact resolve eq22041 eq1095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22041
  have eq117375 : ∀ X0 X1 : G, (σ (k (k (τ X0) X1) (M.op (M.op x y) (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3239 X0 X1
       have i₂ := eq1218 sF1 (k X0 (σ X1))
       grind)
    | exact superpose eq1218 eq3239
    | exact resolve eq3239 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3239
  have eq117376 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (k X0 (σ X1))) = (σ (M.op (M.op (M.op x y) (M.op x y)) (k (τ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq117375 X0 X1
       have i₂ := eq1218 sF0 (k (τ X0) X1)
       grind)
    | exact superpose eq1218 eq117375
    | exact resolve eq117375 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117375
  have eq130593 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (k X1 (σ (M.op X0 X0)))) = (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op X0 X0) (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq117376 X1 (M.op X0 X0)
       have i₂ := eq1218 X0 (τ X1)
       grind)
    | exact superpose eq1218 eq117376
    | exact resolve eq117376 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218 eq117376
  have eq130696 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (k X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq130593 x X1
       have i₂ := eq1501 sF0 (τ X1) x
       grind)
    | exact superpose eq1501 eq130593
    | exact resolve eq130593 eq1501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130593
  have eq130743 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (k X1 (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq130696 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq130696
    | exact resolve eq130696 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130696
  have eq130886 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | exact superpose eq130743 eq372
    | exact resolve eq372 eq130743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq130743
  have eq132008 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq130886 X1 x X2
       have i₂ := eq1239 X0 x
       grind)
    | exact superpose eq1239 eq130886
    | exact resolve eq130886 eq1239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239 eq130886
  have eq242290 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op (M.op X0 X0) X1)) = (M.op X4 (M.op (M.op X7 X7) (M.op (M.op X6 X6) (M.op X1 (M.op X4 (M.op X5 X5)))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq5580 X4 (M.op (M.op X6 X6) (M.op X1 (M.op X4 (M.op X5 X5)))) X2 X3 X5 X7
       have i₂ := eq1510 (M.op X4 (M.op X5 X5)) X1 X0 X6
       grind)
    | exact superpose eq1510 eq5580
    | exact resolve eq5580 eq1510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1510
  have eq242823 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq426 X2 X0 x x x
       have i₂ := eq5580 X0 X2 x x x X1
       grind)
    | (have i₁ := eq426 X1 (M.op X2 X2) X2 x x
       have i₂ := eq5580 (M.op (M.op x x) (M.op x x)) X1 X2 x x (M.op X2 X2)
       grind)
    | exact superpose eq5580 eq426
    | exact resolve eq426 eq5580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq243570 : ∀ X0 X1 X2 X3 X4 X6 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X2 (M.op X3 X3)) (M.op X4 X2))) (M.op X6 X6)) = X4 := by
    intro X0 X1 X2 X3 X4 X6
    first
    | (have i₁ := eq6838 X2 x x X4 X6
       have i₂ := eq5580 X2 (M.op X4 X2) X0 X1 X3 (M.op x x)
       grind)
    | (have i₁ := eq6838 (M.op (M.op X2 X2) (M.op X3 X3)) X1 X4 X3 x
       have i₂ := eq5580 (M.op X1 X1) (M.op X3 (M.op (M.op X2 X2) (M.op X3 X3))) X2 X3 X4 x
       grind)
    | exact superpose eq5580 eq6838
    | exact resolve eq6838 eq5580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5580
  have eq245111 : ∀ X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X3)) (M.op X4 X2)) = X4 := by
    intro X2 X3 X4
    first
    | (have i₁ := eq243570 x x X2 X3 X4 x
       have i₂ := eq925 x x x (M.op (M.op X2 (M.op X3 X3)) (M.op X4 X2))
       grind)
    | exact superpose eq925 eq243570
    | exact resolve eq243570 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925 eq243570
  have eq246093 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op (M.op X0 X0) X1)) = (M.op X4 (M.op X1 (M.op X4 (M.op X5 X5)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq242290 X0 X1 X2 X3 X4 X5 x x
       have i₂ := eq1501 x (M.op X1 (M.op X4 (M.op X5 X5))) x
       grind)
    | exact superpose eq1501 eq242290
    | exact resolve eq242290 eq1501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501 eq242290
  have eq247112 : ∀ X1 X4 X5 : G, (M.op X4 (M.op X1 (M.op X4 (M.op X5 X5)))) = X1 := by
    intro X1 X4 X5
    first
    | (have i₁ := eq246093 x X1 x x X4 X5
       have i₂ := eq1503 x x X1 x
       grind)
    | exact superpose eq1503 eq246093
    | exact resolve eq246093 eq1503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246093
  have eq251208 : ∀ X0 : G, x = (M.op (M.op y (M.op X0 X0)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq245111 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq245111
    | (have j0 := eq245111 y X0 x
       grind)
    | exact resolve eq245111 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251241 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op X0 X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq245111
    | (have j0 := eq245111 (σ y) X0 (σ x)
       grind)
    | exact resolve eq245111 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245111
  have eq252291 : ∀ X0 : G, x = (M.op (M.op y (σ (M.op X0 X0))) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq251208 x
       have i₂ := eq969 X0 x
       grind)
    | exact superpose eq969 eq251208
    | exact resolve eq251208 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252408 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq251208 x
       have i₂ := eq1095 y X0 x
       grind)
    | exact superpose eq1095 eq251208
    | exact resolve eq251208 eq1095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095
  have eq252639 : ∀ X0 : G, (σ x) = (M.op (k (σ y) (τ (M.op X0 X0))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq251241 x
       have i₂ := eq132008 X0 sF3 x
       grind)
    | exact superpose eq132008 eq251241
    | exact resolve eq251241 eq132008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132008
  have eq258168 : ∀ X0 : G, (σ x) = (M.op (k (σ y) (σ (σ (M.op X0 X0)))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq252639 x
       have i₂ := eq2228 X0 x
       grind)
    | exact superpose eq2228 eq252639
    | exact resolve eq252639 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2228 eq252639
  have eq258219 : ∀ X0 : G, (σ x) = (M.op (σ (k y (σ (M.op X0 X0)))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq36 eq258168
    | exact resolve eq258168 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq258168
  have eq610896 : ∀ X0 : G, (σ x) = (M.op (σ (M.op (σ (M.op X0 X0)) y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq258219 X0
       have i₂ := eq8304 X0 y
       grind)
    | exact superpose eq8304 eq258219
    | exact resolve eq258219 eq8304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8304 eq258219
  have eq765416 : ∀ X0 X1 X2 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (σ (M.op y (M.op X0 X0))))) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op y (M.op X0 X0)))) ∨ (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op y (M.op X0 X0))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq251208 eq9500
    | (have j0 := eq9500 (M.op y (M.op X0 X0)) (M.op x y) X2 x
       grind)
    | exact resolve eq9500 eq251208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9500 eq251208
  have eq767354 : ∀ X0 X1 X2 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (M.op (M.op (σ x) (σ x)) (σ y)))) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op y (M.op X0 X0)))) ∨ (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op y (M.op X0 X0))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq765416 X0 X1 X2
       have i₂ := eq22038 X0
       grind)
    | exact superpose eq22038 eq765416
    | (have j0 := eq765416 X0 X1 X2
       grind)
    | exact resolve eq765416 eq22038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765416
  have eq767676 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op y (M.op X0 X0)))) ∨ (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op y (M.op X0 X0))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq767354 X0 X0 x
       have i₂ := eq1503 X0 x sF3 sF2
       grind)
    | exact superpose eq1503 eq767354
    | (have j0 := eq767354 X0 x x
       grind)
    | exact resolve eq767354 eq1503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503 eq767354
  have eq767932 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op y (M.op X0 X0)))) ∨ (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op y (M.op X0 X0))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq767676 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq767676
    | (have j0 := eq767676 X0
       grind)
    | exact resolve eq767676 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767676
  have eq768155 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op y (M.op X0 X0)))) ∨ (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op y (M.op X0 X0))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq26 eq767932
    | (have j0 := eq767932 X0
       grind)
    | exact resolve eq767932 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767932
  have eq768288 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op y (M.op X0 X0)))) ∨ (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op y (M.op X0 X0))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq768155
    | (have j0 := eq768155 X0
       grind)
    | exact resolve eq768155 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768155
  have eq768388 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op y (M.op X0 X0)))) ∨ (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op y (M.op X0 X0))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq768288 X0
       grind)
    | (have r₁ := eq768288 X0
       have r₂ := eq27
       grind)
    | exact resolve eq768288 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768288
  have eq768465 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ x)) (σ y))) ∨ (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op y (M.op X0 X0))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq768388 X0
       have i₂ := eq22038 X0
       grind)
    | exact superpose eq22038 eq768388
    | (have j0 := eq768388 X0
       grind)
    | exact resolve eq768388 eq22038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22038 eq768388
  have eq768513 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ x)) (σ y))) ∨ (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op y (M.op X0 X0))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq768465
    | (have j0 := eq768465 X0
       grind)
    | exact resolve eq768465 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768465
  have eq768545 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ x)) (σ y))) ∨ (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op y (M.op X0 X0))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq135 eq768513
    | (have j0 := eq768513 X0
       grind)
    | exact resolve eq768513 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768513
  have eq768572 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ x)) (σ y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op y (M.op X0 X0))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq135 eq768545
    | (have j0 := eq768545 X0
       grind)
    | exact resolve eq768545 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq768545
  have eq768590 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ x)) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op y (M.op X0 X0))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq768572
    | (have j0 := eq768572 X0
       grind)
    | exact resolve eq768572 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768572
  have eq768637 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op y (M.op X0 X0))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq768590 eq242823
    | (have j1 := eq768590 X0
       grind)
    | exact resolve eq242823 eq768590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242823 eq768590
  have eq768954 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op y (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq768637 eq247112
    | exact resolve eq247112 eq768637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768637
  have eq769152 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq768954 eq251241
    | exact resolve eq251241 eq768954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251241 eq768954
  have eq769289 : ∀ X0 : G, (M.op (M.op y X0) (M.op x y)) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq769152 eq1096
    | exact resolve eq1096 eq769152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096 eq769152
  have eq783163 : ∀ X0 : G, x = (σ (M.op X0 X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq252291 eq769289
    | exact resolve eq769289 eq252291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252291 eq769289
  have eq792936 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq610896 x
       have i₂ := eq783163 x
       grind)
    | exact superpose eq783163 eq610896
    | exact resolve eq610896 eq783163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610896 eq783163
  have eq793336 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq792936
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq792936
    | exact resolve eq792936 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792936
  have eq793485 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq793336
    | exact resolve eq793336 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793336
  have eq793486 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq793485
  have eq793535 : ∀ X0 X1 X2 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (σ x))) (M.op X2 X2)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq793486 eq6838
    | exact resolve eq6838 eq793486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6838 eq793486
  have eq793559 : ∀ X2 : G, (σ (M.op x y)) = (M.op (σ y) (M.op X2 X2)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X2
    first
    | exact superpose eq425 eq793535
    | exact resolve eq793535 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425 eq793535
  have eq793781 : (τ (σ (M.op x y))) = (M.op (M.op x x) y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq793559 eq65996
    | exact resolve eq65996 eq793559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65996 eq793559
  have eq793944 : (M.op x y) = (M.op (M.op x x) y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq30 eq793781
    | exact resolve eq793781 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793781
  have eq817695 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq252408 x
       have i₂ := eq793944
       grind)
    | exact superpose eq793944 eq252408
    | exact resolve eq252408 eq793944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252408 eq793944
  have eq817811 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq817695 eq157
    | exact resolve eq157 eq817695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq817695
  have eq818862 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq30 eq817811
    | exact resolve eq817811 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq817811
  have eq818863 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq818862
  have eq819360 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op X0 X0)))) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq818863 eq4595
    | exact resolve eq4595 eq818863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4595 eq818863
  have eq820150 : x = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq819360 x
       have i₂ := eq247112 x sF0 x
       grind)
    | exact superpose eq247112 eq819360
    | exact resolve eq819360 eq247112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247112 eq819360
  have eq820344 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq820150 eq969
    | exact resolve eq969 eq820150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969 eq820150
  have eq821370 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq820344 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq820344
    | (have j0 := eq820344 X0
       grind)
    | exact resolve eq820344 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820344
  have eq825296 : (M.op (σ x) (σ y)) = (σ (M.op (τ (σ x)) y)) ∨ x = y := by
    first
    | (have i₁ := eq44250 x
       have i₂ := eq821370 x
       grind)
    | exact superpose eq821370 eq44250
    | exact resolve eq44250 eq821370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44250 eq821370
  have eq826459 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28 eq825296
    | exact resolve eq825296 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq825296
  have eq826646 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq826459
    | exact resolve eq826459 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826459
  have eq826674 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq826646
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq826646
    | exact resolve eq826646 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826646
  have eq826678 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq826674
    | exact resolve eq826674 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826674
  have eq826679 : x = y := by
    first
    | (have r₁ := eq826678
       have r₂ := eq27
       grind)
    | exact resolve eq826678 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826678
  have eq827572 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq826679
       grind)
    | exact superpose eq826679 eq18
    | exact resolve eq18 eq826679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq827573 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq826679
       grind)
    | exact superpose eq826679 eq24
    | exact resolve eq24 eq826679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq826679
  have eq827970 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq827573
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq827573
    | exact resolve eq827573 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq827573
  have eq828029 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq827970 eq26
    | exact resolve eq26 eq827970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq827970
  have eq829992 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq828029 eq110
    | exact resolve eq110 eq828029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq828029
  have eq831203 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq829992
       have i₂ := eq827572
       grind)
    | exact superpose eq827572 eq829992
    | exact resolve eq829992 eq827572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827572 eq829992
  have eq831396 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq831203 eq15
    | exact resolve eq15 eq831203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831203
  have eq831991 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq831396
    | exact resolve eq831396 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq831396
  have eq832147 : False := by grind
  exact eq832147

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_pyx_pxy_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq14 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq70 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
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
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq70
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq70
    | exact resolve eq70 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq74 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq73
    | exact resolve eq73 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq271 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq35
  have eq282 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq271 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq271
    | exact resolve eq271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq283 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq282
  have eq409 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (σ (M.op X0 X0))) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (σ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 X2 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq54
    | exact resolve eq54 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq482 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       have i₂ := eq14 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 x (M.op X0 X0) X2
       have i₂ := eq54 x (M.op X0 X0) X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq597 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq283 X0
       grind)
    | exact superpose eq283 eq16
    | exact resolve eq16 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq723 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 X2 (τ X0)
       have i₂ := eq597 X0
       grind)
    | exact superpose eq597 eq54
    | exact resolve eq54 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq981 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op X1 X1))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X3 (M.op X0 (M.op X1 X1)) x
       have i₂ := eq482 X0 X1 x
       grind)
    | exact superpose eq482 eq14
    | exact resolve eq14 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq1568 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (σ (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq564 (M.op X0 (σ (M.op X1 X1))) X0 X2
       have i₂ := eq409 X1 X0 (M.op X0 (σ (M.op X1 X1)))
       grind)
    | exact superpose eq409 eq564
    | exact resolve eq564 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409 eq564
  have eq8026 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq981 X1 (τ X0) X2
       have i₂ := eq597 X0
       grind)
    | exact superpose eq597 eq981
    | exact resolve eq981 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597 eq981
  have eq62524 : ∀ X0 : G, x = (M.op (M.op x x) (M.op y (σ (M.op X0 X0)))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1568 y X0 x
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq1568
    | exact resolve eq1568 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq1568
  have eq62530 : x = y ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq62524 x
       have i₂ := eq479 x x y
       grind)
    | exact superpose eq479 eq62524
    | exact resolve eq62524 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479 eq62524
  have eq62531 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq62530
  have eq62551 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq62531 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq62531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62531
  have eq62552 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq62551
    | exact resolve eq62551 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62551
  have eq62563 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq62552
       have r₂ := eq28
       grind)
    | exact resolve eq62552 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62552
  have eq62577 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (τ (M.op X0 X0)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq62563 eq8026
    | exact resolve eq8026 eq62563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8026 eq62563
  have eq62580 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq62577 x
       have i₂ := eq723 x sF2 sF3
       grind)
    | exact superpose eq723 eq62577
    | exact resolve eq62577 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq62577
  have eq62581 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq62580
  have eq62592 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq62581 eq30
    | exact resolve eq30 eq62581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq62581
  have eq62719 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq62592
    | exact resolve eq62592 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq62592
  have eq62720 : x = y := by grind
  clear eq62719
  have eq63099 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq62720
       grind)
    | exact superpose eq62720 eq19
    | exact resolve eq19 eq62720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq63100 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq62720
       grind)
    | exact superpose eq62720 eq25
    | exact resolve eq25 eq62720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq62720
  have eq63228 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq63100
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq63100
    | exact resolve eq63100 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq63100
  have eq63260 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq63228 eq27
    | exact resolve eq27 eq63228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq63228
  have eq64555 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq63260 eq66
    | exact resolve eq66 eq63260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq63260
  have eq64878 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq64555
       have i₂ := eq63099
       grind)
    | exact superpose eq63099 eq64555
    | exact resolve eq64555 eq63099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63099 eq64555
  have eq64893 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq64878 eq15
    | exact resolve eq15 eq64878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64878
  have eq64974 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq64893
    | exact resolve eq64893 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq64893
  have eq64997 : False := by grind
  exact eq64997

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_x_pxy_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq14 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
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
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq75
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq75
    | exact resolve eq75 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq82 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq81
    | exact resolve eq81 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq271 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq35
  have eq282 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq271 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq271
    | exact resolve eq271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq283 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq282
  have eq409 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (σ (M.op X0 X0))) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (σ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 X2 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq54
    | exact resolve eq54 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq482 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       have i₂ := eq14 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 x (M.op X0 X0) X2
       have i₂ := eq54 x (M.op X0 X0) X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq597 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq283 X0
       grind)
    | exact superpose eq283 eq16
    | exact resolve eq16 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq723 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 X2 (τ X0)
       have i₂ := eq597 X0
       grind)
    | exact superpose eq597 eq54
    | exact resolve eq54 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq981 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op X1 X1))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X3 (M.op X0 (M.op X1 X1)) x
       have i₂ := eq482 X0 X1 x
       grind)
    | exact superpose eq482 eq14
    | exact resolve eq14 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq1568 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (σ (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq564 (M.op X0 (σ (M.op X1 X1))) X0 X2
       have i₂ := eq409 X1 X0 (M.op X0 (σ (M.op X1 X1)))
       grind)
    | exact superpose eq409 eq564
    | exact resolve eq564 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409 eq564
  have eq8155 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq981 X1 (τ X0) X2
       have i₂ := eq597 X0
       grind)
    | exact superpose eq597 eq981
    | exact resolve eq981 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597 eq981
  have eq62535 : ∀ X0 : G, x = (M.op (M.op x x) (M.op y (σ (M.op X0 X0)))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1568 y X0 x
       have i₂ := eq82
       grind)
    | exact superpose eq82 eq1568
    | exact resolve eq1568 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq1568
  have eq62541 : x = y ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq62535 x
       have i₂ := eq479 x x y
       grind)
    | exact superpose eq479 eq62535
    | exact resolve eq62535 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479 eq62535
  have eq62542 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq62541
  have eq62562 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq62542 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq62542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62542
  have eq62563 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq62562
    | exact resolve eq62562 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62562
  have eq62574 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq62563
       have r₂ := eq28
       grind)
    | exact resolve eq62563 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62563
  have eq62588 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (τ (M.op X0 X0)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq62574 eq8155
    | exact resolve eq8155 eq62574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8155 eq62574
  have eq62591 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq62588 x
       have i₂ := eq723 x sF2 sF3
       grind)
    | exact superpose eq723 eq62588
    | exact resolve eq62588 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq62588
  have eq62592 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq62591
  have eq62603 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq62592 eq30
    | exact resolve eq30 eq62592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq62592
  have eq62730 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq62603
    | exact resolve eq62603 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq62603
  have eq62731 : x = y := by grind
  clear eq62730
  have eq63110 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq62731
       grind)
    | exact superpose eq62731 eq19
    | exact resolve eq19 eq62731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq63111 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq62731
       grind)
    | exact superpose eq62731 eq25
    | exact resolve eq25 eq62731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq62731
  have eq63239 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq63111
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq63111
    | exact resolve eq63111 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq63111
  have eq63271 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq63239 eq27
    | exact resolve eq27 eq63239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq63239
  have eq64566 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq63271 eq66
    | exact resolve eq66 eq63271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq63271
  have eq64889 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq64566
       have i₂ := eq63110
       grind)
    | exact superpose eq63110 eq64566
    | exact resolve eq64566 eq63110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63110 eq64566
  have eq64904 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq64889 eq15
    | exact resolve eq15 eq64889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64889
  have eq64985 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq64904
    | exact resolve eq64904 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq64904
  have eq65008 : False := by grind
  exact eq65008

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_y_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq25 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq9 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq18
  have eq53 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq48 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48
    | exact resolve eq48 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq53
  have eq86 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq25 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1153 : ∀ X0 X2 : G, (M.op X2 X2) = (M.op X0 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq25 x (M.op X0 X0) X0
       have i₂ := eq86 (M.op X0 X0) x X2
       grind)
    | (have i₁ := eq25 (M.op X2 X2) (M.op X2 X2) X2
       have i₂ := eq86 X0 x (M.op (M.op X2 X2) (M.op X2 X2))
       grind)
    | exact superpose eq86 eq25
    | exact resolve eq25 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq86
  have eq1200 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 x X0
       have r₂ := eq1153 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq1153 X0 x
       grind)
    | exact resolve eq13 eq1153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1288 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1200 (σ X0) (σ X1)
       grind)
    | exact superpose eq1200 eq15
    | (have j1 := eq1200 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1296 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1288 X0 X1
       have i₂ := eq1200 X0 X1
       grind)
    | exact superpose eq1200 eq1288
    | (have j0 := eq1288 X0 X1
       have j1 := eq1200 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq1288 eq1200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200 eq1288
  have eq1870 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X1
       have i₂ := eq1153 X0 (τ X1)
       grind)
    | (have i₁ := eq54 X1
       have i₂ := eq1153 (τ X1) X0
       grind)
    | exact superpose eq1153 eq54
    | exact resolve eq54 eq1153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1153
  have eq3702 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1296 x y
       grind)
    | exact superpose eq1296 eq16
    | (have j1 := eq1296 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1296 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1296 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq1296 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq1296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1296
  have eq3711 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq3702
  have eq5768 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3711
       grind)
    | exact superpose eq3711 eq10
    | exact resolve eq10 eq3711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3711
  have eq5791 : x = y ∨ x = y := by
    first
    | (have i₁ := eq5768
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5768
    | exact resolve eq5768 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5768
  have eq5792 : x = y := by grind
  clear eq5791
  have eq9046 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5792
       grind)
    | exact superpose eq5792 eq16
    | exact resolve eq16 eq5792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5792
  have eq9047 : False := by grind
  exact eq9047

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_x_pyx_pxx_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq29 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq15
    | (have j0 := eq15 X0 (M.op x y)
       grind)
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq9 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq9 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq32 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32
    | (have j0 := eq32 y
       grind)
    | exact resolve eq32 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq102 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 : G, (σ (k (M.op x y) (k X0 (τ X1)))) = (k (σ (M.op x y)) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 (k X0 (τ X1))
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq29
    | exact resolve eq29 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq219 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq60 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq60 eq60
    | exact resolve eq60 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq60 X1 (M.op X0 X0) X0
       grind)
    | exact superpose eq60 eq9
    | exact resolve eq9 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 X2 : G, (M.op X2 X2) = (M.op X0 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq60 x (M.op X0 X0) X0
       have i₂ := eq219 (M.op X0 X0) x X2
       grind)
    | (have i₁ := eq60 (M.op X2 X2) (M.op X2 X2) X2
       have i₂ := eq219 X0 x (M.op (M.op X2 X2) (M.op X2 X2))
       grind)
    | exact superpose eq219 eq60
    | exact resolve eq60 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X2 X2)) X1 X2
       have i₂ := eq246 X0 (M.op X1 (M.op X2 X2))
       grind)
    | (have i₁ := eq9 (M.op X1 (M.op X2 X2)) X1 X2
       have i₂ := eq246 (M.op X1 (M.op X2 X2)) X0
       grind)
    | exact superpose eq246 eq9
    | exact resolve eq9 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) ≠ (M.op (M.op X0 X0) (M.op X1 X1)) ∨ X2 = X3 ∨ (k X2 X3) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X2 X3
       have i₂ := eq219 X1 X0 X3
       grind)
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq219 X0 X0 X2
       grind)
    | exact superpose eq219 eq13
    | (have j0 := eq13 X2 X3
       grind)
    | (have r₁ := eq13 X2 (M.op X0 X0)
       have r₂ := eq219 X0 X0 X2
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X2
       have r₂ := eq219 X0 X0 X2
       grind)
    | exact resolve eq13 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X2 X3 : G, (k X2 X3) = (M.op X3 X2) ∨ X2 = X3 := by
    intro X2 X3
    first
    | (have j0 := eq362 x x X2 X3
       grind)
    | (have r₁ := eq362 x x X2 X3
       have r₂ := eq219 x x X2
       grind)
    | (have r₁ := eq362 x x (M.op x x) X3
       have r₂ := eq219 x x (M.op x x)
       grind)
    | exact resolve eq362 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq362
  have eq444 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq372 sF3 sF2
       grind)
    | exact superpose eq372 eq70
    | (have j1 := eq372 (M.op (σ x) (σ y)) (σ (k y x))
       grind)
    | exact resolve eq70 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq448 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq444
    | exact resolve eq444 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq450 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq448
       have i₂ := eq372 y x
       grind)
    | exact superpose eq372 eq448
    | (have j1 := eq372 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq448 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq461 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq450
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq450
    | exact resolve eq450 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq462 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq461
    | exact resolve eq461 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq463 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq462
       have r₂ := eq28
       grind)
    | exact resolve eq462 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq468 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq463 eq44
    | exact resolve eq44 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq463
  have eq475 : x = y ∨ x = y := by
    first
    | exact superpose eq43 eq468
    | exact resolve eq468 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq468
  have eq476 : x = y := by grind
  clear eq475
  have eq480 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq476
       grind)
    | exact superpose eq476 eq19
    | exact resolve eq19 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq481 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq476
       grind)
    | exact superpose eq476 eq25
    | exact resolve eq25 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq476
  have eq519 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq481
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq481
    | exact resolve eq481 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq481
  have eq528 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq519 eq27
    | exact resolve eq27 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq519
  have eq552 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq60 x X0 X1
       have i₂ := eq480
       grind)
    | exact superpose eq480 eq60
    | exact resolve eq60 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq558 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq246 x X0
       have i₂ := eq480
       grind)
    | exact superpose eq480 eq246
    | exact resolve eq246 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq480
  have eq562 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op x y)) X0)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq59 X0 X1 x X3
       have i₂ := eq558 x
       grind)
    | exact superpose eq558 eq59
    | exact resolve eq59 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq568 : ∀ X1 X2 : G, (M.op (M.op (M.op x y) X2) (M.op X1 X1)) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq224 x X1 X2
       have i₂ := eq558 x
       grind)
    | exact superpose eq558 eq224
    | exact resolve eq224 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq576 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X1 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq288 X0 X1 x
       have i₂ := eq558 x
       grind)
    | exact superpose eq558 eq288
    | exact resolve eq288 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq579 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq528
       have i₂ := eq558 sF2
       grind)
    | exact superpose eq558 eq528
    | exact resolve eq528 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq582 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq552 X0 x
       have i₂ := eq558 x
       grind)
    | exact superpose eq558 eq552
    | exact resolve eq552 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq584 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq579 eq28
    | exact resolve eq28 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq579
  have eq587 : ∀ X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op x y) X1) := by
    intro X1
    first
    | (have i₁ := eq576 x X1
       have i₂ := eq558 x
       grind)
    | exact superpose eq558 eq576
    | exact resolve eq576 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq594 : ∀ X2 : G, (M.op (M.op (M.op x y) X2) (M.op x y)) = X2 := by
    intro X2
    first
    | (have i₁ := eq568 x X2
       have i₂ := eq558 x
       grind)
    | exact superpose eq558 eq568
    | exact resolve eq568 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq599 : ∀ X0 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op x y) (M.op x y)) X0)) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq562 X0 x X3
       have i₂ := eq558 x
       grind)
    | exact superpose eq558 eq562
    | exact resolve eq562 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq609 : ∀ X2 : G, (M.op (M.op x y) (M.op (M.op x y) X2)) = X2 := by
    intro X2
    first
    | exact superpose eq587 eq594
    | exact resolve eq594 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq613 : ∀ X0 X3 : G, (M.op (M.op X0 X3) (M.op (M.op x y) X0)) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq599 X0 X3
       have i₂ := eq558 sF0
       grind)
    | exact superpose eq558 eq599
    | exact resolve eq599 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq599
  have eq2235 : ∀ X0 X1 : G, (k (σ (M.op x y)) (k (σ X0) X1)) = (σ (M.op (k X0 (τ X1)) (M.op x y))) ∨ (M.op x y) = (k X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq103 X0 X1
       have i₂ := eq372 sF0 (k X0 (τ X1))
       grind)
    | exact superpose eq372 eq103
    | (have j1 := eq372 (k (σ (M.op x y)) (k (σ X0) X1)) (σ (M.op (k X0 (τ X1)) (M.op x y)))
       grind)
    | exact resolve eq103 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq2266 : ∀ X0 X1 : G, (k (σ (M.op x y)) (k (σ X0) X1)) = (σ (M.op (M.op x y) (k X0 (τ X1)))) ∨ (M.op x y) = (k X0 (τ X1)) := by
    intro X0 X1
    first
    | exact superpose eq587 eq2235
    | (have j0 := eq2235 X0 X1
       grind)
    | exact resolve eq2235 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587 eq2235
  have eq7283 : ∀ X0 : G, (k (σ (M.op x y)) (k (σ X0) (σ (M.op x y)))) = (σ (M.op (M.op x y) (k X0 (M.op x y)))) ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq42 eq2266
    | exact resolve eq2266 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7307 : ∀ X0 : G, (k (σ (M.op x y)) (σ (k X0 (M.op x y)))) = (σ (M.op (M.op x y) (k X0 (M.op x y)))) ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq31 eq7283
    | (have j0 := eq7283 X0
       grind)
    | exact resolve eq7283 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7283
  have eq7317 : ∀ X0 : G, (σ (k (M.op x y) (k X0 (M.op x y)))) = (σ (M.op (M.op x y) (k X0 (M.op x y)))) ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq29 eq7307
    | (have j0 := eq7307 X0
       grind)
    | exact resolve eq7307 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq7307
  have eq8045 : ∀ X0 : G, (k (M.op x y) (k X0 (M.op x y))) = (τ (σ (M.op (M.op x y) (k X0 (M.op x y))))) ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq7317 eq10
    | (have j1 := eq7317 X0
       grind)
    | exact resolve eq10 eq7317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7317
  have eq8069 : ∀ X0 : G, (k (M.op x y) (k X0 (M.op x y))) = (M.op (M.op x y) (k X0 (M.op x y))) ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq8045 X0
       have i₂ := eq10 (M.op sF0 (k X0 sF0))
       grind)
    | exact superpose eq10 eq8045
    | (have j0 := eq8045 X0
       grind)
    | exact resolve eq8045 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8045
  have eq8071 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (k (M.op x y) (M.op (M.op x y) X0)) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq8069 x
       have i₂ := eq372 x sF0
       grind)
    | exact superpose eq372 eq8069
    | (have j1 := eq372 (M.op (M.op x y) (M.op (M.op x y) X0)) (k (M.op x y) (M.op (M.op x y) X0))
       grind)
    | exact resolve eq8069 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8069
  have eq8084 : ∀ X0 : G, (k (M.op x y) (M.op (M.op x y) X0)) = X0 ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq8071 X0
       have i₂ := eq609 (M.op sF0 (M.op sF0 X0))
       grind)
    | exact superpose eq609 eq8071
    | (have j0 := eq8071 X0
       grind)
    | exact resolve eq8071 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8071
  have eq8090 : ∀ X0 : G, (k (M.op x y) X0) = (M.op (M.op x y) X0) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq609 eq8084
    | (have j0 := eq8084 X0
       grind)
    | exact resolve eq8084 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8084
  have eq8160 : ∀ X0 : G, (k (σ (M.op x y)) (k (σ (M.op x y)) X0)) = (σ (M.op (M.op x y) (M.op (M.op x y) (τ X0)))) ∨ (M.op x y) = (M.op (M.op x y) (τ X0)) ∨ (τ X0) = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq8090 eq2266
    | (have j1 := eq8090 (τ X0)
       grind)
    | exact resolve eq2266 eq8090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266 eq8090
  have eq8168 : ∀ X0 : G, (k (σ (M.op x y)) (k (σ (M.op x y)) X0)) = (σ (M.op (M.op x y) (M.op (M.op x y) (τ X0)))) ∨ (M.op x y) = (M.op (M.op x y) (τ X0)) ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq8160 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8160
  have eq8195 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op x y)) (k (σ (M.op x y)) X0)) ∨ (M.op x y) = (M.op (M.op x y) (τ X0)) ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8168 X0
       have i₂ := eq609 (M.op sF0 (M.op sF0 (τ X0)))
       grind)
    | exact superpose eq609 eq8168
    | (have j0 := eq8168 X0
       grind)
    | exact resolve eq8168 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8168
  have eq8209 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op x y)) (k (σ (M.op x y)) X0)) ∨ (M.op x y) = (M.op (M.op x y) (τ X0)) ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21 eq8195
    | (have j0 := eq8195 X0
       grind)
    | exact resolve eq8195 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8195
  have eq8210 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (τ X0)) ∨ (k (σ (M.op x y)) (k (σ (M.op x y)) X0)) = X0 ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8209 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8209
    | (have j0 := eq8209 X0
       grind)
    | exact resolve eq8209 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8209
  have eq8852 : ∀ X0 : G, (τ X0) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ (k (σ (M.op x y)) (k (σ (M.op x y)) X0)) = X0 ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8210 eq613
    | (have j1 := eq8210 X0
       grind)
    | exact resolve eq613 eq8210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8210
  have eq8853 : ∀ X0 : G, (τ X0) = (M.op x y) ∨ (k (σ (M.op x y)) (k (σ (M.op x y)) X0)) = X0 ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq582 eq8852
    | (have j0 := eq8852 X0
       grind)
    | exact resolve eq8852 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq8852
  have eq8854 : ∀ X0 : G, (τ X0) = (M.op x y) ∨ (k (σ (M.op x y)) (k (σ (M.op x y)) X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq8853 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8853
  have eq8884 : ∀ X0 : G, (σ (M.op x y)) = X0 ∨ (k (σ (M.op x y)) (k (σ (M.op x y)) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0
       have i₂ := eq8854 X0
       grind)
    | exact superpose eq8854 eq11
    | (have j1 := eq8854 X0
       grind)
    | exact resolve eq11 eq8854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8854
  have eq8904 : ∀ X0 : G, (k (σ (M.op x y)) (k (σ (M.op x y)) X0)) = X0 ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq21 eq8884
    | (have j0 := eq8884 X0
       grind)
    | exact resolve eq8884 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq8884
  have eq8919 : ∀ X0 : G, (σ (τ X0)) = (k (σ (σ (M.op x y))) (k (σ (σ (M.op x y))) X0)) ∨ (τ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq8904 eq102
    | (have j1 := eq8904 (τ X0)
       grind)
    | exact resolve eq102 eq8904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq8904
  have eq8924 : ∀ X0 : G, (τ X0) = (σ (M.op x y)) ∨ (k (σ (σ (M.op x y))) (k (σ (σ (M.op x y))) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq8919 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8919
    | (have j0 := eq8919 X0
       grind)
    | exact resolve eq8919 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8919
  have eq10369 : (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (σ (M.op x y))) (k (σ (σ (M.op x y))) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq42
       have i₂ := eq8924 sF1
       grind)
    | exact superpose eq8924 eq42
    | (have j1 := eq8924 (σ (M.op x y))
       grind)
    | exact resolve eq42 eq8924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8924
  have eq10372 : (σ (M.op x y)) = (k (σ (σ (M.op x y))) (k (σ (σ (M.op x y))) (σ (M.op x y)))) := by
    first
    | (have r₁ := eq10369
       have r₂ := eq584
       grind)
    | exact resolve eq10369 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10369
  have eq10382 : (σ (M.op x y)) = (k (σ (σ (M.op x y))) (σ (k (σ (M.op x y)) (M.op x y)))) := by
    first
    | exact superpose eq31 eq10372
    | exact resolve eq10372 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq10372
  have eq10387 : (σ (M.op x y)) = (σ (k (σ (M.op x y)) (k (σ (M.op x y)) (M.op x y)))) := by
    first
    | (have i₁ := eq10382
       have i₂ := eq15 sF1 (k sF1 sF0)
       grind)
    | exact superpose eq15 eq10382
    | exact resolve eq10382 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10382
  have eq10392 : (τ (σ (M.op x y))) = (k (σ (M.op x y)) (k (σ (M.op x y)) (M.op x y))) := by
    first
    | exact superpose eq10387 eq10
    | exact resolve eq10 eq10387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10387
  have eq10409 : (M.op x y) = (k (σ (M.op x y)) (k (σ (M.op x y)) (M.op x y))) := by
    first
    | exact superpose eq42 eq10392
    | exact resolve eq10392 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq10392
  have eq10725 : (M.op x y) = (M.op (k (σ (M.op x y)) (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq10409 eq372
    | (have j0 := eq372 (M.op x y) (M.op (k (σ (M.op x y)) (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq372 eq10409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq11037 : (σ (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (k (σ (M.op x y)) (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq10725 eq613
    | exact resolve eq613 eq10725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613 eq10725
  have eq11039 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq11037
       have i₂ := eq609 (M.op sF0 (M.op sF0 (k sF1 sF0)))
       grind)
    | exact superpose eq609 eq11037
    | exact resolve eq11037 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609 eq11037
  have eq11040 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op x y)) := by grind
  clear eq11039
  have eq11044 : (M.op x y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq11040 eq10409
    | exact resolve eq10409 eq11040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10409 eq11040
  have eq11082 : (M.op x y) = (σ (M.op x y)) := by grind
  clear eq11044
  have eq11090 : False := by grind
  exact eq11090

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_x_pyx_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq14 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq86 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq86
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq86
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq86 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
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
  have eq100 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq99
    | exact resolve eq99 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq271 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq35
  have eq282 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq271 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq271
    | exact resolve eq271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq283 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq282
  have eq409 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (σ (M.op X0 X0))) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (σ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 X2 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq54
    | exact resolve eq54 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq483 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       have i₂ := eq14 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 x (M.op X0 X0) X2
       have i₂ := eq54 x (M.op X0 X0) X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq598 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq283 X0
       grind)
    | exact superpose eq283 eq16
    | exact resolve eq16 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq718 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 X2 (τ X0)
       have i₂ := eq598 X0
       grind)
    | exact superpose eq598 eq54
    | exact resolve eq54 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq981 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op X1 X1))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X3 (M.op X0 (M.op X1 X1)) x
       have i₂ := eq483 X0 X1 x
       grind)
    | exact superpose eq483 eq14
    | exact resolve eq14 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq1568 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (σ (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq565 (M.op X0 (σ (M.op X1 X1))) X0 X2
       have i₂ := eq409 X1 X0 (M.op X0 (σ (M.op X1 X1)))
       grind)
    | exact superpose eq409 eq565
    | exact resolve eq565 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409 eq565
  have eq8159 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq981 X1 (τ X0) X2
       have i₂ := eq598 X0
       grind)
    | exact superpose eq598 eq981
    | exact resolve eq981 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598 eq981
  have eq62441 : ∀ X0 : G, x = (M.op (M.op x x) (M.op y (σ (M.op X0 X0)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1568 y X0 x
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq1568
    | exact resolve eq1568 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq1568
  have eq62447 : x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq62441 x
       have i₂ := eq480 x x y
       grind)
    | exact superpose eq480 eq62441
    | exact resolve eq62441 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480 eq62441
  have eq62448 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq62447
  have eq62468 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq62448 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq62448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62448
  have eq62469 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq62468
    | exact resolve eq62468 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62468
  have eq62480 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq62469
       have r₂ := eq28
       grind)
    | exact resolve eq62469 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62469
  have eq62494 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (τ (M.op X0 X0)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq62480 eq8159
    | exact resolve eq8159 eq62480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8159 eq62480
  have eq62497 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq62494 x
       have i₂ := eq718 x sF2 sF3
       grind)
    | exact superpose eq718 eq62494
    | exact resolve eq62494 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718 eq62494
  have eq62498 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq62497
  have eq62509 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq62498 eq30
    | exact resolve eq30 eq62498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq62498
  have eq62636 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq62509
    | exact resolve eq62509 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq62509
  have eq62637 : x = y := by grind
  clear eq62636
  have eq63013 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq62637
       grind)
    | exact superpose eq62637 eq19
    | exact resolve eq19 eq62637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq63014 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq62637
       grind)
    | exact superpose eq62637 eq25
    | exact resolve eq25 eq62637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq62637
  have eq63142 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq63014
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq63014
    | exact resolve eq63014 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq63014
  have eq63174 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq63142 eq27
    | exact resolve eq27 eq63142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq63142
  have eq64466 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq63174 eq66
    | exact resolve eq66 eq63174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq63174
  have eq64789 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq64466
       have i₂ := eq63013
       grind)
    | exact superpose eq63013 eq64466
    | exact resolve eq64466 eq63013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63013 eq64466
  have eq64804 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq64789 eq15
    | exact resolve eq15 eq64789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64789
  have eq64885 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq64804
    | exact resolve eq64804 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq64804
  have eq64908 : False := by grind
  exact eq64908

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_y_pyx_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq14 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq86 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq86
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq86
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq86 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
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
  have eq100 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq99
    | exact resolve eq99 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq271 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq35
  have eq282 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq271 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq271
    | exact resolve eq271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq283 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq282
  have eq409 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (σ (M.op X0 X0))) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (σ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 X2 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq54
    | exact resolve eq54 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq483 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       have i₂ := eq14 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 x (M.op X0 X0) X2
       have i₂ := eq54 x (M.op X0 X0) X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq598 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq283 X0
       grind)
    | exact superpose eq283 eq16
    | exact resolve eq16 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq723 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 X2 (τ X0)
       have i₂ := eq598 X0
       grind)
    | exact superpose eq598 eq54
    | exact resolve eq54 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq981 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op X1 X1))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X3 (M.op X0 (M.op X1 X1)) x
       have i₂ := eq483 X0 X1 x
       grind)
    | exact superpose eq483 eq14
    | exact resolve eq14 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq1568 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (σ (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq565 (M.op X0 (σ (M.op X1 X1))) X0 X2
       have i₂ := eq409 X1 X0 (M.op X0 (σ (M.op X1 X1)))
       grind)
    | exact superpose eq409 eq565
    | exact resolve eq565 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409 eq565
  have eq8159 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq981 X1 (τ X0) X2
       have i₂ := eq598 X0
       grind)
    | exact superpose eq598 eq981
    | exact resolve eq981 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598 eq981
  have eq62446 : ∀ X0 : G, x = (M.op (M.op x x) (M.op y (σ (M.op X0 X0)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1568 y X0 x
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq1568
    | exact resolve eq1568 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq1568
  have eq62452 : x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq62446 x
       have i₂ := eq480 x x y
       grind)
    | exact superpose eq480 eq62446
    | exact resolve eq62446 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480 eq62446
  have eq62453 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq62452
  have eq62473 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq62453 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq62453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62453
  have eq62474 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq62473
    | exact resolve eq62473 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62473
  have eq62485 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq62474
       have r₂ := eq28
       grind)
    | exact resolve eq62474 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62474
  have eq62499 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (τ (M.op X0 X0)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq62485 eq8159
    | exact resolve eq8159 eq62485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8159 eq62485
  have eq62502 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq62499 x
       have i₂ := eq723 x sF2 sF3
       grind)
    | exact superpose eq723 eq62499
    | exact resolve eq62499 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq62499
  have eq62503 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq62502
  have eq62514 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq62503 eq30
    | exact resolve eq30 eq62503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq62503
  have eq62641 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq62514
    | exact resolve eq62514 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq62514
  have eq62642 : x = y := by grind
  clear eq62641
  have eq63018 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq62642
       grind)
    | exact superpose eq62642 eq19
    | exact resolve eq19 eq62642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq63019 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq62642
       grind)
    | exact superpose eq62642 eq25
    | exact resolve eq25 eq62642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq62642
  have eq63147 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq63019
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq63019
    | exact resolve eq63019 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq63019
  have eq63179 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq63147 eq27
    | exact resolve eq27 eq63147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq63147
  have eq64471 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq63179 eq66
    | exact resolve eq66 eq63179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq63179
  have eq64794 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq64471
       have i₂ := eq63018
       grind)
    | exact superpose eq63018 eq64471
    | exact resolve eq64471 eq63018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63018 eq64471
  have eq64809 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq64794 eq15
    | exact resolve eq15 eq64794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64794
  have eq64890 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq64809
    | exact resolve eq64809 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq64809
  have eq64913 : False := by grind
  exact eq64913
