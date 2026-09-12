import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxy_pxx_pxy_Equation4430 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4430 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq57 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X2 X3 (M.op x X5) X5
       have i₂ := eq14 X0 X1 x X5
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 (M.op y y) y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq76
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq76
    | exact resolve eq76 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq79
    | exact resolve eq79 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq92 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq96 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq92
  have eq97 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq96
  have eq128 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq16
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq210 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq58 X0 (M.op X0 x)
       have i₂ := eq58 X0 x
       grind)
    | exact superpose eq58 eq58
    | exact resolve eq58 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq58 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq58
    | (have j0 := eq58 x y
       grind)
    | exact resolve eq58 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq58 x x
       have i₂ := eq14 x x X0 X1
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq396 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq58 (σ X0) (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq58
    | exact resolve eq58 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq401 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq213 eq396
    | exact resolve eq396 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq403 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq213 eq210
    | exact resolve eq210 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq404 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq213 eq215
    | exact resolve eq215 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq547 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op x y) y) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq57 x x X2 X3 X5
       have i₂ := eq58 x x
       grind)
    | exact superpose eq58 eq57
    | exact resolve eq57 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq548 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X2 X3 X5
    first
    | exact superpose eq213 eq547
    | exact resolve eq547 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq549 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | (have i₁ := eq548 x x X5
       have i₂ := eq58 x x
       grind)
    | exact superpose eq58 eq548
    | exact resolve eq548 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq548
  have eq550 : ∀ X5 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | exact superpose eq213 eq549
    | exact resolve eq549 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq549
  have eq998 : (M.op x (M.op x y)) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq550 eq401
    | exact resolve eq401 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401 eq550
  have eq1023 : (M.op x (M.op x y)) = (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq998
       have i₂ := eq45 (M.op x sF0)
       grind)
    | exact superpose eq45 eq998
    | exact resolve eq998 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq998
  have eq1039 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq403 eq1023
    | exact resolve eq1023 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq10704 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq80 eq11
    | (have j0 := eq11 (M.op (σ y) (σ y)) (σ y)
       grind)
    | exact resolve eq11 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq10705 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq10704
    | exact resolve eq10704 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10704
  have eq10716 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq10705
       have r₂ := eq28
       grind)
    | exact resolve eq10705 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10705
  have eq10720 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq10716 eq128
    | exact resolve eq128 eq10716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq10716
  have eq10754 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq30 eq10720
    | exact resolve eq10720 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10720
  have eq10755 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10754
  have eq10897 : (M.op y y) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq404 y y
       have i₂ := eq10755
       grind)
    | exact superpose eq10755 eq404
    | exact resolve eq404 eq10755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq10974 : y = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10755
       have i₂ := eq10897
       grind)
    | exact superpose eq10897 eq10755
    | exact resolve eq10755 eq10897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10755 eq10897
  have eq10986 : y = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10974
  have eq11140 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq10986 eq403
    | exact resolve eq403 eq10986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11143 : y = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10986 eq1039
    | exact resolve eq1039 eq10986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039 eq10986
  have eq11174 : (σ x) = (σ y) ∨ y = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11143
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11143
    | exact resolve eq11143 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11143
  have eq11180 : y = (τ (σ x)) ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq11174 eq30
    | exact resolve eq30 eq11174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11174
  have eq11291 : x = y ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq11180
    | exact resolve eq11180 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11180
  have eq11292 : y = (σ y) ∨ x = y := by grind
  clear eq11291
  have eq11312 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ x = y := by
    first
    | exact superpose eq11292 eq27
    | exact resolve eq27 eq11292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12323 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq11140 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11140
    | (have j0 := eq11140 x
       grind)
    | exact resolve eq11140 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11140
  have eq12397 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12323 eq30
    | exact resolve eq30 eq12323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12323
  have eq12527 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq12397
    | exact resolve eq12397 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12397
  have eq12528 : y = (M.op x y) ∨ x = y := by grind
  clear eq12527
  have eq12675 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq12528 eq21
    | exact resolve eq21 eq12528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12728 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq12528 eq403
    | exact resolve eq403 eq12528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq12765 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq12728 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12728
    | (have j0 := eq12728 X0
       grind)
    | exact resolve eq12728 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12728
  have eq12818 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12675
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12675
    | exact resolve eq12675 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12675
  have eq12911 : y = (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq12818 eq11292
    | exact resolve eq11292 eq12818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11292 eq12818
  have eq12922 : y = (σ (M.op x y)) ∨ x = y := by grind
  clear eq12911
  have eq13671 : ∀ X0 : G, y = (M.op X0 y) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq12528 eq12765
    | exact resolve eq12765 eq12528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12528 eq12765
  have eq13727 : ∀ X0 : G, y = (M.op X0 y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq13671 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13671
  have eq13996 : y = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq11312
       have i₂ := eq13727 sF2
       grind)
    | exact superpose eq13727 eq11312
    | exact resolve eq11312 eq13727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11312 eq13727
  have eq13999 : y = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq13996
  have eq14039 : y ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq13999 eq28
    | exact resolve eq28 eq13999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13999
  have eq14047 : x = y := by
    first
    | (have r₁ := eq14039
       have r₂ := eq12922
       grind)
    | exact resolve eq14039 eq12922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12922 eq14039
  have eq14049 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq14047
       grind)
    | exact superpose eq14047 eq19
    | exact resolve eq19 eq14047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq14050 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq14047
       grind)
    | exact superpose eq14047 eq25
    | exact resolve eq25 eq14047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq14047
  have eq14156 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq14050
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14050
    | exact resolve eq14050 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq14050
  have eq14173 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq14156 eq27
    | exact resolve eq27 eq14156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq14156
  have eq14384 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq14173 eq72
    | exact resolve eq72 eq14173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq14173
  have eq14414 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq14384
       have i₂ := eq14049
       grind)
    | exact superpose eq14049 eq14384
    | exact resolve eq14384 eq14049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14049 eq14384
  have eq14425 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14414 eq15
    | exact resolve eq15 eq14414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14414
  have eq14473 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq14425
    | exact resolve eq14425 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq14425
  have eq14482 : False := by grind
  exact eq14482

/-- `Equation4440`: `x ◇ (y ◇ x) = (x ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pxy_pxx_pxy_Equation4440 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4440 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4440.models_iff G M).mp hM
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X2) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq99 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq45 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq45
    | (have j0 := eq45 y
       grind)
    | exact resolve eq45 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
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
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 (M.op X0 X2) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X0 x X3
       have i₂ := eq16 X0 x X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (M.op x y) y) := by
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
  have eq182 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X0 X2 x
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
  have eq184 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op x (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq180 (M.op X0 x)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq180
    | exact resolve eq180 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op x X1) X1) := by
    intro X1
    first
    | (have i₁ := eq16 x x X1
       have i₂ := eq180 x
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op x X0) X1
       have i₂ := eq186 X0
       grind)
    | (have i₁ := eq16 y (M.op x y) x
       have i₂ := eq186 X1
       grind)
    | exact superpose eq186 eq16
    | exact resolve eq16 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : (M.op (M.op x y) y) = (M.op x (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq180 (M.op x x)
       have i₂ := eq186 x
       grind)
    | exact superpose eq186 eq180
    | exact resolve eq180 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq186
  have eq715 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq182 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq182
    | (have j0 := eq182 y X0 x
       grind)
    | exact resolve eq182 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq865 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X0 X0) X0) := by
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
  have eq985 : (M.op x y) = (k x y) ∨ y = (M.op y y) := by
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
  have eq995 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq1000 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1060 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq985
       grind)
    | exact superpose eq985 eq41
    | exact resolve eq41 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq1061 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1060
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1060
    | exact resolve eq1060 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060
  have eq1063 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1061
    | exact resolve eq1061 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061
  have eq1073 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1063 eq995
    | exact resolve eq995 eq1063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995 eq1063
  have eq1080 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1073
       have r₂ := eq27
       grind)
    | exact resolve eq1073 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq1087 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1080 eq183
    | exact resolve eq183 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1102 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1080 eq1087
    | exact resolve eq1087 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080 eq1087
  have eq1114 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1102 eq153
    | exact resolve eq153 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq1102
  have eq1117 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq32 eq1114
    | exact resolve eq1114 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq1120 : y = (M.op y y) := by
    first
    | (have j1 := eq1000 y
       grind)
    | (have r₁ := eq1117
       have r₂ := eq1000 y
       grind)
    | exact resolve eq1117 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117
  have eq1124 : (M.op y (M.op x y)) = (M.op y y) := by
    first
    | (have i₁ := eq715 y
       have i₂ := eq1120
       grind)
    | exact superpose eq1120 eq715
    | exact resolve eq715 eq1120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1125 : ∀ X0 : G, y ≠ y ∨ y = X0 ∨ (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq1120
       grind)
    | exact superpose eq1120 eq12
    | (have j0 := eq12 (k X0 y) X0
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq1120
       grind)
    | exact resolve eq12 eq1120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1126 : (k y y) = (M.op y y) := by
    first
    | (have i₁ := eq183 y
       have i₂ := eq1120
       grind)
    | exact superpose eq1120 eq183
    | exact resolve eq183 eq1120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1133 : (M.op (M.op x y) y) = (M.op x (M.op y y)) := by
    first
    | (have i₁ := eq184 y y
       have i₂ := eq1120
       grind)
    | exact superpose eq1120 eq184
    | exact resolve eq184 eq1120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq1134 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq1125 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq1135 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq1133
       have i₂ := eq1120
       grind)
    | exact superpose eq1120 eq1133
    | exact resolve eq1133 eq1120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133
  have eq1141 : y = (k y y) := by
    first
    | (have i₁ := eq1126
       have i₂ := eq1120
       grind)
    | exact superpose eq1120 eq1126
    | exact resolve eq1126 eq1120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq1142 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1124
       have i₂ := eq1120
       grind)
    | exact superpose eq1120 eq1124
    | exact resolve eq1124 eq1120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120 eq1124
  have eq1143 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq1135
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1135
    | exact resolve eq1135 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1135
  have eq1157 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq1141
       grind)
    | exact superpose eq1141 eq41
    | exact resolve eq41 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1141
  have eq1160 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1157
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1157
    | exact resolve eq1157 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq1187 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq1143 eq202
    | exact resolve eq202 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq1191 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | exact superpose eq1143 eq177
    | exact resolve eq177 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1196 : (M.op (M.op x y) y) = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq1191 x
       have i₂ := eq201 sF0 x
       grind)
    | exact superpose eq201 eq1191
    | exact resolve eq1191 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191
  have eq1199 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1143 eq1196
    | exact resolve eq1196 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196
  have eq1205 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1160 eq1000
    | (have j0 := eq1000 (σ y)
       grind)
    | (have r₁ := eq1000 (σ y)
       have r₂ := eq1160
       grind)
    | exact resolve eq1000 eq1160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000 eq1160
  have eq1206 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1205
  have eq1212 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1187 eq16
    | exact resolve eq16 eq1187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1224 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq1199 eq1212
    | exact resolve eq1212 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199 eq1212
  have eq1231 : (M.op x y) = (k (M.op x x) x) := by
    first
    | (have i₁ := eq1224 x
       have i₂ := eq865 x x
       grind)
    | exact superpose eq865 eq1224
    | exact resolve eq1224 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865 eq1224
  have eq1262 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = X0 ∨ (M.op X0 X0) = (k X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq1206 eq12
    | (have j0 := eq12 (k X0 (σ y)) X0
       grind)
    | (have r₁ := eq12 X0 (σ y)
       have r₂ := eq1206
       grind)
    | exact resolve eq12 eq1206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1267 : ∀ X0 : G, (M.op (M.op (σ y) X0) X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq1206 eq177
    | exact resolve eq177 eq1206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq1271 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) ∨ (σ y) = X0 := by
    intro X0
    first
    | (have j0 := eq1262 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262
  have eq1275 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) X0) := by
    intro X0
    first
    | exact superpose eq1206 eq1267
    | exact resolve eq1267 eq1206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206 eq1267
  have eq1283 : (σ y) = (M.op (σ y) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq1275 x
       have i₂ := eq201 sF3 x
       grind)
    | exact superpose eq201 eq1275
    | exact resolve eq1275 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275
  have eq1288 : (σ y) = (M.op (σ y) (M.op x y)) := by
    first
    | exact superpose eq1143 eq1283
    | exact resolve eq1283 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283
  have eq1604 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X4) X4) = (M.op X3 (M.op X5 (M.op X0 (M.op X1 (M.op X2 X1))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq176 X5 (M.op X0 X5) X3 X4
       have i₂ := eq176 X1 X2 X0 X5
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1648 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X0 (M.op y (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq176 y x X0 X1
       have i₂ := eq715 x
       grind)
    | (have i₁ := eq176 y x x x
       have i₂ := eq715 X0
       grind)
    | exact superpose eq715 eq176
    | (have j0 := eq176 y x X0 X1
       grind)
    | exact resolve eq176 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq1670 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) X4) = (M.op X3 (M.op X0 (M.op X1 (M.op X2 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X3 (M.op X0 X3) X4
       have i₂ := eq176 X1 X2 X0 X3
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1727 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 (M.op X2 X1)))) = (M.op X3 (M.op (M.op x y) y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1670 X0 X1 X2 X3 x
       have i₂ := eq201 X3 x
       grind)
    | exact superpose eq201 eq1670
    | exact resolve eq1670 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1670
  have eq1738 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X0 y) := by
    intro X0 X1
    first
    | exact superpose eq1142 eq1648
    | exact resolve eq1648 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648
  have eq1777 : ∀ X0 X1 X2 X3 X5 : G, (M.op X3 (M.op X5 (M.op X0 (M.op X1 (M.op X2 X1))))) = (M.op X3 (M.op (M.op x y) y)) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq1604 X0 X1 X2 X3 x X5
       have i₂ := eq201 X3 x
       grind)
    | exact superpose eq201 eq1604
    | exact resolve eq1604 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq1604
  have eq1829 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 (M.op X2 X1)))) = (M.op X3 (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1143 eq1727
    | exact resolve eq1727 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727
  have eq1857 : ∀ X0 X1 X2 X3 X5 : G, (M.op X3 (M.op X5 (M.op X0 (M.op X1 (M.op X2 X1))))) = (M.op X3 (M.op x y)) := by
    intro X0 X1 X2 X3 X5
    first
    | exact superpose eq1143 eq1777
    | exact resolve eq1777 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143 eq1777
  have eq1898 : ∀ X3 X5 : G, (M.op X3 (M.op x y)) = (M.op X3 (M.op X5 (M.op x y))) := by
    intro X3 X5
    first
    | (have i₁ := eq1857 x x x X3 X5
       have i₂ := eq1829 x x x X5
       grind)
    | exact superpose eq1829 eq1857
    | exact resolve eq1857 eq1829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1829 eq1857
  have eq3057 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1142 eq1898
    | exact resolve eq1898 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3059 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1288 eq1898
    | exact resolve eq1898 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1898
  have eq3357 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq3059 eq26
    | (have j1 := eq3059 (σ x)
       grind)
    | exact resolve eq26 eq3059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3059
  have eq3848 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq183 X0
       have i₂ := eq1738 X0 X0
       grind)
    | exact superpose eq1738 eq183
    | exact resolve eq183 eq1738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq1738
  have eq3903 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq3848 X0
       have i₂ := eq3057 X0
       grind)
    | exact superpose eq3057 eq3848
    | exact resolve eq3848 eq3057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3057 eq3848
  have eq4131 : (k (τ (M.op (σ x) (σ x))) x) = (τ (M.op (σ x) (M.op x y))) := by
    first
    | (have i₁ := eq142 (M.op sF2 sF2)
       have i₂ := eq3903 sF2
       grind)
    | exact superpose eq3903 eq142
    | exact resolve eq142 eq3903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq3903
  have eq4134 : (k (τ (M.op (σ x) (σ x))) x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3357 eq4131
    | exact resolve eq4131 eq3357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4131
  have eq6993 : (M.op x y) = (k (k x y) x) ∨ x = y := by
    first
    | (have i₁ := eq1231
       have i₂ := eq1134 x
       grind)
    | exact superpose eq1134 eq1231
    | (have j1 := eq1134 x
       grind)
    | exact resolve eq1231 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134 eq1231
  have eq13537 : (τ (M.op (σ x) (σ y))) = (k (τ (k (σ x) (σ y))) x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4134
       have i₂ := eq1271 sF2
       grind)
    | exact superpose eq1271 eq4134
    | (have j1 := eq1271 (σ x)
       grind)
    | exact resolve eq4134 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271 eq4134
  have eq13551 : (τ (M.op (σ x) (σ y))) = (k (k x y) x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq99 eq13537
    | exact resolve eq13537 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq13537
  have eq31769 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6993
       have i₂ := eq13551
       grind)
    | exact superpose eq13551 eq6993
    | exact resolve eq6993 eq13551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6993 eq13551
  have eq31786 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq31769 eq14
    | exact resolve eq14 eq31769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31769
  have eq31787 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq31786
    | exact resolve eq31786 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31786
  have eq31791 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq31787
       have r₂ := eq27
       grind)
    | exact resolve eq31787 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31787
  have eq31793 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq31791 eq32
    | exact resolve eq32 eq31791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq31791
  have eq31897 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq31793
    | exact resolve eq31793 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq31793
  have eq31898 : x = y := by grind
  clear eq31897
  have eq31910 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq31898
       grind)
    | exact superpose eq31898 eq24
    | exact resolve eq24 eq31898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq31923 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1142
       have i₂ := eq31898
       grind)
    | exact superpose eq31898 eq1142
    | exact resolve eq1142 eq31898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142 eq31898
  have eq31979 : x = (M.op x y) := by
    first
    | exact superpose eq1187 eq31923
    | exact resolve eq31923 eq1187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187 eq31923
  have eq31990 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq31910
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31910
    | exact resolve eq31910 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31910
  have eq31999 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq31979
       grind)
    | exact superpose eq31979 eq22
    | exact resolve eq22 eq31979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq31979
  have eq32132 : (σ x) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq31990 eq1288
    | exact resolve eq1288 eq31990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288 eq31990
  have eq32277 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq31999 eq20
    | exact resolve eq20 eq31999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq31999
  have eq32559 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32132 eq3357
    | exact resolve eq3357 eq32132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3357 eq32132
  have eq32636 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq32559 eq27
    | exact resolve eq27 eq32559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq32559
  have eq32767 : False := by grind
  exact eq32767

/-- `Equation4440`: `x ◇ (y ◇ x) = (x ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_x_pxx_pxy_Equation4440 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4440 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4440.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X2) := by
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
  clear eq43
  have eq53 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X0 X2) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X0 x X3
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 X0)) = (M.op (M.op (M.op X0 X1) X1) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 X2 (M.op X3 X0)
       have i₂ := eq14 X0 X3 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X3 (M.op X0 X2))) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X2) X3 X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (M.op x y) y) := by
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
  have eq65 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq76 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq101 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq111 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq64 x
       have i₂ := eq14 x x X0
       grind)
    | exact superpose eq14 eq64
    | exact resolve eq64 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq65 (M.op X0 sF2)
       have i₂ := eq14 X0 X1 sF2
       grind)
    | exact superpose eq14 eq65
    | exact resolve eq65 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq65 x
       have i₂ := eq14 sF2 x x
       grind)
    | exact superpose eq14 eq65
    | exact resolve eq65 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq233 : ∀ X0 X1 : G, (σ (k (k (τ X0) X1) x)) = (k (k X0 (σ X1)) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq39
    | exact resolve eq39 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq329 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq342 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X2) X3) X3) = (M.op (M.op (M.op X0 X1) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 (M.op X0 X2) X2 X3
       have i₂ := eq61 X0 X2 X1
       grind)
    | (have i₁ := eq61 (M.op X0 X2) X2 X3
       have i₂ := eq61 X0 X1 X2
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X0 X2) X3
       have i₂ := eq61 X0 X2 X1
       grind)
    | (have i₁ := eq14 X2 (M.op X0 X2) X3
       have i₂ := eq61 X0 X1 X2
       grind)
    | exact superpose eq61 eq14
    | exact resolve eq14 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op x (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (M.op X0 x)
       have i₂ := eq61 X0 x X1
       grind)
    | (have i₁ := eq64 (M.op X0 x)
       have i₂ := eq61 X0 X1 x
       grind)
    | exact superpose eq61 eq64
    | exact resolve eq64 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq65 (M.op X0 sF2)
       have i₂ := eq61 X0 sF2 x
       grind)
    | (have i₁ := eq65 (M.op X0 sF2)
       have i₂ := eq61 X0 X1 sF2
       grind)
    | exact superpose eq61 eq65
    | exact resolve eq65 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq406 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq66 X2 (M.op X0 X2) X3
       have i₂ := eq61 X0 X2 X1
       grind)
    | (have i₁ := eq66 X2 (M.op X0 X2) X3
       have i₂ := eq61 X0 X1 X2
       grind)
    | exact superpose eq61 eq66
    | exact resolve eq66 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq66 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq66
    | (have j0 := eq66 y x X0
       grind)
    | exact resolve eq66 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq66
    | (have j0 := eq66 (σ y) X0 (σ x)
       grind)
    | exact resolve eq66 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) X3) = (M.op (M.op X0 (M.op X1 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 (M.op X2 X0) X3
       have i₂ := eq66 X0 X2 X1
       grind)
    | (have i₁ := eq61 X0 (M.op X2 X0) X3
       have i₂ := eq66 X0 X1 X2
       grind)
    | exact superpose eq66 eq61
    | exact resolve eq61 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq461 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq111 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq111
    | (have j0 := eq111 (σ X0)
       grind)
    | exact resolve eq111 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq475 : ∀ X0 X1 : G, (M.op y (M.op x y)) = (M.op y (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq411 (M.op X0 y)
       have i₂ := eq14 X0 X1 y
       grind)
    | exact superpose eq14 eq411
    | exact resolve eq411 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : ∀ X0 X1 : G, (M.op y (M.op X0 y)) = (M.op (M.op y (M.op x y)) (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 y X0 (M.op X1 y)
       have i₂ := eq411 X1
       grind)
    | (have i₁ := eq14 y X1 (M.op x y)
       have i₂ := eq411 X0
       grind)
    | exact superpose eq411 eq14
    | exact resolve eq14 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X1 : G, (M.op y (M.op x y)) = (M.op (M.op y (M.op x y)) (M.op X1 y)) := by
    intro X1
    first
    | (have i₁ := eq486 x X1
       have i₂ := eq411 x
       grind)
    | (have i₁ := eq486 x X1
       have i₂ := eq411 x
       grind)
    | exact superpose eq411 eq486
    | (have j0 := eq486 x X1
       grind)
    | exact resolve eq486 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq492 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X2 X0)) = (M.op X0 (M.op X3 (M.op X4 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq60 X3 X4 X0 (M.op X2 X0)
       have i₂ := eq66 X0 X2 X1
       grind)
    | (have i₁ := eq60 X3 X4 X0 (M.op X2 X0)
       have i₂ := eq66 X0 X1 X2
       grind)
    | exact superpose eq66 eq60
    | exact resolve eq60 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq522 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X0 (M.op y (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq60 y x X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq60
    | (have j0 := eq60 y x X0 X1
       grind)
    | exact resolve eq60 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op (M.op X0 X0) X0) ∨ (k X2 (M.op (M.op X0 X0) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 X0) X0)
       have i₂ := eq62 X0 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq62 eq13
    | (have j0 := eq13 X2 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq13 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq705 : ∀ X0 X2 : G, (k X2 (M.op (M.op X0 X0) X0)) = X2 := by
    intro X0 X2
    first
    | (have j0 := eq695 X0 x X2
       grind)
    | (have r₁ := eq695 X2 x X2
       have r₂ := eq14 X2 x X2
       grind)
    | exact resolve eq695 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq728 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq705 x X0
       have i₂ := eq200 x
       grind)
    | exact superpose eq200 eq705
    | exact resolve eq705 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq729 : ∀ X0 : G, (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq207 eq705
    | exact resolve eq705 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq705
  have eq743 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq728 eq34
    | exact resolve eq34 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq746 : ∀ X0 : G, (k X0 (σ (M.op (M.op x y) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq743 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq743
    | exact resolve eq743 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq977 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 (M.op X1 X0)) X2) = (M.op (M.op X0 (M.op X4 X0)) X2) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq63 X0 X4 X2 x
       have i₂ := eq63 X0 X1 X2 x
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1005 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X2) X3) (M.op X4 (M.op (M.op X0 X2) X3))) = (M.op (M.op (M.op X0 (M.op X1 X0)) X2) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq63 (M.op X0 X2) x X3 X4
       have i₂ := eq63 X0 X1 X2 x
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1006 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) y) X0) = (M.op (M.op x X0) (M.op X1 (M.op x X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq63 x x X0 X1
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq63
    | exact resolve eq63 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq1016 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) X4) = (M.op X3 (M.op (M.op X0 (M.op X1 X0)) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq60 (M.op X0 X2) x X3 X4
       have i₂ := eq63 X0 X1 X2 x
       grind)
    | exact superpose eq63 eq60
    | exact resolve eq60 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq1297 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq76 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X0)
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq76 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq76 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq12 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1332 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1334 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1297 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297
  have eq1335 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1334 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334
  have eq1337 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1335 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq1335
    | (have j0 := eq1335 X0 X1
       grind)
    | exact resolve eq1335 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335
  have eq1585 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq229 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq229
    | (have j0 := eq229 X0 x
       grind)
    | exact resolve eq229 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq1671 : (k (k x x) x) = (τ (k (k (σ x) (σ x)) (σ x))) := by
    first
    | exact superpose eq49 eq1585
    | exact resolve eq1585 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq1585
  have eq1730 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    intro X0
    first
    | exact superpose eq729 eq329
    | exact resolve eq329 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329 eq729
  have eq1762 : ∀ X0 : G, (k X0 (τ (M.op (M.op (σ x) (σ y)) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1730 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq1730
    | exact resolve eq1730 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1730
  have eq4483 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op X2 (M.op X0 (M.op y (M.op x y)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq365 X0 x X2 X3
       have i₂ := eq522 X0 x
       grind)
    | exact superpose eq522 eq365
    | exact resolve eq365 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq4484 : ∀ X0 X2 : G, (M.op X2 (M.op y (M.op x y))) = (M.op X2 (M.op X0 (M.op y (M.op x y)))) := by
    intro X0 X2
    first
    | (have i₁ := eq4483 X0 X2 x
       have i₂ := eq522 X2 x
       grind)
    | exact superpose eq522 eq4483
    | exact resolve eq4483 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4483
  have eq4667 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op X2 (M.op X0 (M.op y (M.op x y)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq406 X0 x X2 X3
       have i₂ := eq522 X0 x
       grind)
    | exact superpose eq522 eq406
    | exact resolve eq406 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq5985 : ∀ X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op X2 (M.op y (M.op x y))) := by
    intro X2 X3
    first
    | exact superpose eq4484 eq4667
    | exact resolve eq4667 eq4484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4667
  have eq7387 : ∀ X0 : G, (k (k X0 (σ (τ X0))) (σ x)) = (σ (k (M.op (τ X0) (τ X0)) x)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq233 X0 (τ X0)
       have i₂ := eq111 (τ X0)
       grind)
    | exact superpose eq111 eq233
    | (have j1 := eq111 (τ X0)
       grind)
    | exact resolve eq233 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq7515 : ∀ X0 : G, (σ (k (M.op (τ X0) (τ X0)) x)) = (k (k X0 X0) (σ x)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq7387 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq7387
    | (have j0 := eq7387 X0
       grind)
    | exact resolve eq7387 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7387
  have eq9656 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X0 X2) X3) X3) = (M.op (M.op X0 (M.op y (M.op x y))) X2) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq342 X0 x X2 X3
       have i₂ := eq522 X0 x
       grind)
    | exact superpose eq522 eq342
    | exact resolve eq342 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq9657 : ∀ X0 X2 : G, (M.op (M.op X0 X2) (M.op y (M.op x y))) = (M.op (M.op X0 (M.op y (M.op x y))) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq9656 X0 X2 x
       have i₂ := eq522 (M.op X0 X2) x
       grind)
    | exact superpose eq522 eq9656
    | exact resolve eq9656 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9656
  have eq10475 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X2 X0)) = (M.op X0 (M.op y (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq441 X0 X1 X2 x
       have i₂ := eq522 X0 x
       grind)
    | exact superpose eq522 eq441
    | exact resolve eq441 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq12541 : ∀ X0 X2 X3 : G, (M.op (M.op X0 (M.op y (M.op x y))) X2) = (M.op (M.op X0 (M.op X3 X0)) X2) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq977 X0 x X2 X3
       have i₂ := eq5985 X0 x
       grind)
    | (have i₁ := eq977 (M.op x y) y X2 x
       have i₂ := eq5985 (M.op x y) X3
       grind)
    | exact superpose eq5985 eq977
    | exact resolve eq977 eq5985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq13350 : ∀ X0 : G, (M.op (M.op (M.op x y) y) X0) = (M.op (M.op x X0) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1006 X0 x
       have i₂ := eq5985 (M.op x X0) x
       grind)
    | (have i₁ := eq1006 y y
       have i₂ := eq5985 (M.op x y) x
       grind)
    | exact superpose eq5985 eq1006
    | exact resolve eq1006 eq5985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006
  have eq13439 : ∀ X0 : G, (M.op (M.op (M.op x y) y) X0) = (M.op (M.op (M.op (M.op x y) y) X0) (M.op y (M.op x y))) := by
    intro X0
    first
    | exact superpose eq13350 eq522
    | exact resolve eq522 eq13350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13350
  have eq14618 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 (M.op X1 X0)) X2)) = (M.op X3 (M.op y (M.op x y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1016 X0 X1 X2 X3 x
       have i₂ := eq522 X3 x
       grind)
    | exact superpose eq522 eq1016
    | exact resolve eq1016 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq15353 : ∀ X0 X1 X2 : G, (M.op X2 (M.op y (M.op x y))) = (M.op X2 (M.op (M.op X0 (M.op y (M.op x y))) X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq9657 eq4484
    | exact resolve eq4484 eq9657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4484 eq9657
  have eq20445 : ∀ X0 X3 X4 : G, (M.op X0 (M.op X3 (M.op X4 X3))) = (M.op X0 (M.op y (M.op x y))) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq492 X0 x x X3 X4
       have i₂ := eq10475 X0 x x
       grind)
    | exact superpose eq10475 eq492
    | exact resolve eq492 eq10475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492 eq10475
  have eq24832 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq461 X0
       grind)
    | exact superpose eq461 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq461 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq461 X0
       grind)
    | exact resolve eq13 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24861 : ∀ X0 : G, (M.op (σ X0) (M.op y (M.op x y))) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq522 (σ X0) (σ X0)
       have i₂ := eq461 X0
       grind)
    | exact superpose eq461 eq522
    | (have j1 := eq461 X0
       grind)
    | exact resolve eq522 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461 eq522
  have eq24914 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq24832 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq24832 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq24832 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24832
  have eq40525 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) X2) X3) = (M.op (M.op (M.op X0 X2) X3) (M.op y (M.op x y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1005 X0 X1 X2 X3 x
       have i₂ := eq5985 (M.op (M.op X0 X2) X3) x
       grind)
    | exact superpose eq5985 eq1005
    | exact resolve eq1005 eq5985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq40649 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op (M.op (M.op X0 X2) X4) X5) (M.op y (M.op x y))) = (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X2) X4) X5) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq40525 (M.op X0 X2) x X4 X5
       have i₂ := eq63 X0 X1 X2 x
       grind)
    | exact superpose eq63 eq40525
    | exact resolve eq40525 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq40525
  have eq49585 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1337 X0 X1
       have j1 := eq1332 X0 X1
       grind)
    | (have r₁ := eq1337 X0 X1
       have r₂ := eq1332 X0 X1
       grind)
    | (have r₁ := eq1337 X0 X0
       have r₂ := eq1332 X0 X0
       grind)
    | exact resolve eq1337 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332 eq1337
  have eq49700 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24914 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq24914
    | (have j0 := eq24914 (τ X0) X1
       grind)
    | exact resolve eq24914 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq49817 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49700 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq49700
    | (have j0 := eq49700 X0 X1
       grind)
    | exact resolve eq49700 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49700
  have eq49873 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49817 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq49817
    | (have j0 := eq49817 X0 X1
       grind)
    | exact resolve eq49817 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49817
  have eq49973 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq49585 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq49585
    | exact resolve eq49585 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50055 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq49585 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq49585
    | (have j0 := eq49585 X0 y
       grind)
    | exact resolve eq49585 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50173 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq49973 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq49973
    | (have j0 := eq49973 X0 X1
       grind)
    | exact resolve eq49973 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq49973
  have eq69963 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq50055 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq50055
    | (have j0 := eq50055 x
       grind)
    | exact resolve eq50055 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50055
  have eq70081 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq69963
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq69963
    | exact resolve eq69963 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69963
  have eq70113 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq70081
    | exact resolve eq70081 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70081
  have eq70488 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq50173 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq50173
    | (have j0 := eq50173 X1 X1
       grind)
    | exact resolve eq50173 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50173
  have eq71527 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq70488 x y
       grind)
    | exact superpose eq70488 eq44
    | (have j1 := eq70488 x y
       grind)
    | exact resolve eq44 eq70488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq71746 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq71527
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq71527
    | exact resolve eq71527 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71527
  have eq71794 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq71746
    | exact resolve eq71746 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71746
  have eq71866 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq71794 eq70113
    | exact resolve eq70113 eq71794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70113 eq71794
  have eq71873 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq71866
       have r₂ := eq27
       grind)
    | exact resolve eq71866 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71866
  have eq71902 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq71873 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq71873
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq71873
       grind)
    | exact resolve eq13 eq71873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71873
  have eq71964 : ∀ X0 : G, y = (M.op y y) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq71902 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71902
  have eq72032 : ∀ X0 X1 : G, y ≠ y ∨ (k X0 y) = X0 ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq71964 X1
       grind)
    | exact superpose eq71964 eq13
    | (have j0 := eq13 X0 y
       have j1 := eq71964 X1
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq71964 X0
       grind)
    | exact resolve eq13 eq71964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71964
  have eq72093 : ∀ X0 X1 : G, (k X1 (σ y)) = X1 ∨ (k X0 y) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq72032 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72032
  have eq72195 : ∀ X0 : G, (τ (σ y)) = (k y y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq101
       have i₂ := eq72093 (k sF3 sF3) x
       grind)
    | exact superpose eq72093 eq101
    | (have j1 := eq72093 X0 x
       grind)
    | exact resolve eq101 eq72093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq72093
  have eq72257 : ∀ X0 : G, y = (k y y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq29 eq72195
    | (have j0 := eq72195 y
       grind)
    | exact resolve eq72195 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq72195
  have eq72303 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq72257 X0
       have j1 := eq49873 y X0
       grind)
    | (have r₁ := eq72257 X0
       have r₂ := eq49873 y x
       grind)
    | (have r₁ := eq72257 y
       have r₂ := eq49873 y x
       grind)
    | exact resolve eq72257 eq49873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49873 eq72257
  have eq72358 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq24914 y X0
       have i₂ := eq72303 y
       grind)
    | exact superpose eq72303 eq24914
    | (have j0 := eq24914 y X0
       grind)
    | exact resolve eq24914 eq72303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24914
  have eq72359 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq111 y
       have i₂ := eq72303 y
       grind)
    | exact superpose eq72303 eq111
    | (have j0 := eq111 y
       grind)
    | exact resolve eq111 eq72303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72381 : y = (M.op y y) := by grind
  clear eq72359
  have eq72382 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq72358 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72358
  have eq72401 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq72382 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq72382
    | (have j0 := eq72382 X0
       grind)
    | exact resolve eq72382 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq72382
  have eq72463 : (M.op y y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq411 y
       have i₂ := eq72381
       grind)
    | exact superpose eq72381 eq411
    | exact resolve eq411 eq72381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq72481 : (M.op (M.op x y) y) = (M.op x (M.op y y)) := by
    first
    | (have i₁ := eq366 y y
       have i₂ := eq72381
       grind)
    | exact superpose eq72381 eq366
    | exact resolve eq366 eq72381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq72571 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq72481
       have i₂ := eq72381
       grind)
    | exact superpose eq72381 eq72481
    | exact resolve eq72481 eq72381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72481
  have eq72588 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq72463
       have i₂ := eq72381
       grind)
    | exact superpose eq72381 eq72463
    | exact resolve eq72463 eq72381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72381 eq72463
  have eq72610 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq72571
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq72571
    | exact resolve eq72571 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72571
  have eq72688 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq72401 eq111
    | (have j0 := eq111 (σ y)
       grind)
    | exact resolve eq111 eq72401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72710 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq72688
  have eq73014 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq72610 eq746
    | exact resolve eq746 eq72610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq73144 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq73014
    | (have j0 := eq73014 X0
       grind)
    | exact resolve eq73014 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73014
  have eq73181 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq72710 eq413
    | exact resolve eq413 eq72710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73200 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq72710 eq367
    | exact resolve eq367 eq72710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq73205 : (M.op y (M.op x y)) = (M.op y (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq72710 eq475
    | exact resolve eq475 eq72710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq73285 : (M.op y (M.op x y)) = (M.op y (σ y)) := by
    first
    | exact superpose eq72710 eq73205
    | exact resolve eq73205 eq72710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73205
  have eq73290 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq72710 eq73200
    | exact resolve eq73200 eq72710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73200
  have eq73308 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq72710 eq73181
    | exact resolve eq73181 eq72710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72710 eq73181
  have eq73334 : y = (M.op y (σ y)) := by
    first
    | exact superpose eq72588 eq73285
    | exact resolve eq73285 eq72588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73285
  have eq73337 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq73290
    | exact resolve eq73290 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq73290
  have eq73769 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq73144 eq111
    | (have j0 := eq111 (σ (M.op x y))
       grind)
    | exact resolve eq111 eq73144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73144
  have eq73791 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq73769
  have eq74063 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) y) := by
    first
    | exact superpose eq73334 eq413
    | exact resolve eq413 eq73334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq74171 : (σ y) = (M.op (σ y) y) := by
    first
    | exact superpose eq73308 eq74063
    | exact resolve eq74063 eq73308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73308 eq74063
  have eq74251 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq73337 eq1762
    | exact resolve eq1762 eq73337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1762
  have eq74809 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq73791 eq66
    | exact resolve eq66 eq73791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74848 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq73791 eq20445
    | exact resolve eq20445 eq73791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20445
  have eq74871 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq73791 eq74848
    | exact resolve eq74848 eq73791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74848
  have eq74910 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq73791 eq74809
    | exact resolve eq74809 eq73791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73791 eq74809
  have eq74929 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq72588 eq74871
    | exact resolve eq74871 eq72588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74871
  have eq75000 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op y (σ y))) := by
    first
    | exact superpose eq74171 eq206
    | exact resolve eq206 eq74171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74171
  have eq75095 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq73334 eq75000
    | exact resolve eq75000 eq73334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73334 eq75000
  have eq75140 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq73337 eq75095
    | exact resolve eq75095 eq73337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75095
  have eq83341 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq74251 eq111
    | (have j0 := eq111 (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq111 eq74251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq74251
  have eq83365 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by grind
  clear eq83341
  have eq93126 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq74929 eq74910
    | exact resolve eq74910 eq74929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74910 eq74929
  have eq96963 : ∀ X0 X2 X3 : G, (M.op (M.op X0 y) X2) = (M.op (M.op X0 (M.op X3 X0)) X2) := by
    intro X0 X2 X3
    first
    | exact superpose eq72588 eq12541
    | exact resolve eq12541 eq72588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12541
  have eq99446 : ∀ X0 : G, (M.op (M.op (M.op x y) y) X0) = (M.op (M.op (M.op (M.op x y) y) X0) y) := by
    intro X0
    first
    | exact superpose eq72588 eq13439
    | exact resolve eq13439 eq72588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13439
  have eq99447 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | exact superpose eq72610 eq99446
    | exact resolve eq99446 eq72610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99446
  have eq99552 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op (M.op y (M.op x y)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq99447 eq491
    | exact resolve eq491 eq99447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491 eq99447
  have eq99683 : ∀ X0 : G, y = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq72588 eq99552
    | exact resolve eq99552 eq72588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99552
  have eq99924 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op x y))) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | exact superpose eq99683 eq14618
    | exact resolve eq14618 eq99683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14618 eq99683
  have eq100104 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | exact superpose eq72588 eq99924
    | exact resolve eq99924 eq72588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99924
  have eq102055 : ∀ X0 X1 X2 : G, (M.op X2 y) = (M.op X2 (M.op (M.op X0 y) X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq72588 eq15353
    | exact resolve eq15353 eq72588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15353
  have eq102137 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq102055 x X0 X0
       have i₂ := eq66 X0 (M.op x y) X1
       grind)
    | (have i₁ := eq102055 x X0 X0
       have i₂ := eq66 X0 X1 (M.op x y)
       grind)
    | exact superpose eq66 eq102055
    | exact resolve eq102055 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq102217 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq206 X0 (M.op x y)
       have i₂ := eq102055 x X0 X0
       grind)
    | exact superpose eq102055 eq206
    | exact resolve eq206 eq102055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq102055
  have eq102719 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq73337 eq102217
    | exact resolve eq102217 eq73337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73337 eq102217
  have eq121321 : (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (M.op (τ (M.op (σ x) (σ y))) (M.op y (M.op x y))) := by
    first
    | exact superpose eq83365 eq5985
    | exact resolve eq5985 eq83365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5985
  have eq121371 : (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (M.op (τ (M.op (σ x) (σ y))) y) := by
    first
    | exact superpose eq72588 eq121321
    | exact resolve eq121321 eq72588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72588 eq121321
  have eq121429 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) y) := by
    first
    | exact superpose eq83365 eq121371
    | exact resolve eq121371 eq83365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83365 eq121371
  have eq426690 : (k (k (k (σ x) (σ y)) (k (σ x) (σ y))) (σ x)) = (σ (k (M.op (k x y) (k x y)) x)) ∨ (k x y) = (M.op (k x y) (k x y)) := by
    first
    | exact superpose eq53 eq7515
    | exact resolve eq7515 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq7515
  have eq426877 : (σ (k (M.op x x) x)) = (k (k (k (σ x) (σ y)) (k (σ x) (σ y))) (σ x)) ∨ (k x y) = (M.op (k x y) (k x y)) := by
    first
    | (have i₁ := eq426690
       have i₂ := eq72303 x
       grind)
    | exact superpose eq72303 eq426690
    | exact resolve eq426690 eq72303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426690
  have eq426952 : (k (k (σ x) (σ x)) (σ x)) = (σ (k (M.op x x) x)) ∨ (k x y) = (M.op (k x y) (k x y)) := by
    first
    | exact superpose eq72401 eq426877
    | exact resolve eq426877 eq72401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72401 eq426877
  have eq427009 : (k (k (σ x) (σ x)) (σ x)) = (σ (k (M.op x x) x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq426952
       have i₂ := eq72303 x
       grind)
    | exact superpose eq72303 eq426952
    | exact resolve eq426952 eq72303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72303 eq426952
  have eq433435 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) y) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq24861 X0
       have i₂ := eq100104 (σ X0) sF0
       grind)
    | exact superpose eq100104 eq24861
    | (have j0 := eq24861 X0
       grind)
    | exact resolve eq24861 eq100104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24861
  have eq433974 : ∀ X0 : G, (M.op (σ X0) y) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq49585 (k X0 X0) X0
       have i₂ := eq433435 X0
       grind)
    | exact superpose eq433435 eq49585
    | (have j0 := eq49585 X0 X0
       have j1 := eq433435 X0
       grind)
    | exact resolve eq49585 eq433435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49585 eq433435
  have eq434069 : ∀ X0 : G, (M.op (σ X0) y) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq433974 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433974
  have eq500868 : ∀ X0 X2 X4 X5 : G, (M.op (M.op (M.op (M.op X0 X2) X4) X5) (M.op y (M.op x y))) = (M.op (M.op (M.op (M.op X0 y) X2) X4) X5) := by
    intro X0 X2 X4 X5
    first
    | (have i₁ := eq40649 X0 x X2 X4 X5
       have i₂ := eq96963 X0 X2 x
       grind)
    | exact superpose eq96963 eq40649
    | exact resolve eq40649 eq96963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40649 eq96963
  have eq500869 : ∀ X0 X2 X4 X5 : G, (M.op (M.op (M.op (M.op X0 y) X2) X4) X5) = (M.op (M.op (M.op (M.op X0 X2) X4) X5) y) := by
    intro X0 X2 X4 X5
    first
    | (have i₁ := eq500868 X0 X2 X4 X5
       have i₂ := eq100104 (M.op (M.op (M.op X0 X2) X4) X5) sF0
       grind)
    | exact superpose eq100104 eq500868
    | exact resolve eq500868 eq100104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100104 eq500868
  have eq502026 : ∀ X0 X1 X2 X3 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (M.op (M.op (M.op X0 y) X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq93126 (M.op (M.op (M.op X0 X1) X2) X3)
       have i₂ := eq500869 X0 X1 X2 X3
       grind)
    | (have i₁ := eq93126 (M.op (M.op (M.op X0 y) X2) x)
       have i₂ := eq500869 X0 X2 x y
       grind)
    | exact superpose eq500869 eq93126
    | exact resolve eq93126 eq500869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93126
  have eq502033 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (M.op X0 y) X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq102719 (M.op (M.op (M.op X0 X1) X2) X3)
       have i₂ := eq500869 X0 X1 X2 X3
       grind)
    | (have i₁ := eq102719 (M.op (M.op (M.op X0 y) X2) x)
       have i₂ := eq500869 X0 X2 x y
       grind)
    | exact superpose eq500869 eq102719
    | exact resolve eq102719 eq500869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102719 eq500869
  have eq678679 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (τ (M.op (σ x) (σ y))) X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq121429 eq502033
    | exact resolve eq502033 eq121429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502033
  have eq1091872 : ∀ X0 X1 X2 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (M.op (M.op (τ (M.op (σ x) (σ y))) X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq121429 eq502026
    | exact resolve eq502026 eq121429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502026
  have eq3395700 : (k (k (σ x) (σ x)) (σ x)) = (σ (M.op (M.op x x) x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq427009
       have i₂ := eq70488 (M.op x x) x
       grind)
    | exact superpose eq70488 eq427009
    | (have j1 := eq70488 x x
       grind)
    | exact resolve eq427009 eq70488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70488 eq427009
  have eq3396069 : (k (k (σ x) (σ x)) (σ x)) = (σ (M.op (M.op x x) x)) ∨ x = (M.op x x) := by grind
  clear eq3395700
  have eq3396120 : (σ (M.op (M.op x y) y)) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3396069
       have i₂ := eq200 x
       grind)
    | exact superpose eq200 eq3396069
    | exact resolve eq3396069 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq3396069
  have eq3396167 : (σ (M.op x y)) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq72610 eq3396120
    | exact resolve eq3396120 eq72610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72610 eq3396120
  have eq3396187 : (σ (M.op x y)) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq3396167
    | exact resolve eq3396167 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3396167
  have eq3396210 : (τ (σ (M.op x y))) = (k (k x x) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3396187 eq1671
    | exact resolve eq1671 eq3396187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1671 eq3396187
  have eq3396292 : (M.op x y) = (k (k x x) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq3396210
    | exact resolve eq3396210 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3396210
  have eq4921698 : (σ (M.op x y)) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq434069 x
       have i₂ := eq3396292
       grind)
    | exact superpose eq3396292 eq434069
    | (have j0 := eq434069 x
       grind)
    | exact resolve eq434069 eq3396292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434069 eq3396292
  have eq4922667 : (σ (M.op x y)) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4921698
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4921698
    | exact resolve eq4921698 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4921698
  have eq4924697 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq75140 eq4922667
    | exact resolve eq4922667 eq75140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4922667
  have eq4926475 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq4924697
    | exact resolve eq4924697 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4924697
  have eq4927727 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq4926475
       have r₂ := eq27
       grind)
    | exact resolve eq4926475 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4926475
  have eq4928700 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4927727
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4927727
    | exact resolve eq4927727 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4927727
  have eq4930980 : (M.op (σ x) (σ x)) = (M.op (σ x) y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4928700 eq102137
    | exact resolve eq102137 eq4928700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4931028 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq75140 eq4930980
    | exact resolve eq4930980 eq75140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75140 eq4930980
  have eq4940315 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4931028 eq4928700
    | exact resolve eq4928700 eq4931028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4928700 eq4931028
  have eq4940445 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4940315
  have eq4940789 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq102137 x x
       have i₂ := eq4940445
       grind)
    | exact superpose eq4940445 eq102137
    | exact resolve eq102137 eq4940445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102137
  have eq4940833 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4940789
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4940789
    | exact resolve eq4940789 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4940789
  have eq4942622 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4940445
       have i₂ := eq4940833
       grind)
    | exact superpose eq4940833 eq4940445
    | exact resolve eq4940445 eq4940833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4940445 eq4940833
  have eq4942733 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4942622
  have eq4943153 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4942733 eq121429
    | exact resolve eq121429 eq4942733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121429 eq4942733
  have eq4944311 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq4943153
    | exact resolve eq4943153 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4943153
  have eq4944392 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4944311
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4944311
    | exact resolve eq4944311 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4944311
  have eq4944393 : x = (M.op x y) := by grind
  clear eq4944392
  have eq4944410 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq4944393 eq20
    | exact resolve eq20 eq4944393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4944393
  have eq4945636 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4944410
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4944410
    | exact resolve eq4944410 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4944410
  have eq4946027 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (M.op (M.op (τ (M.op (σ x) (σ y))) X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq4945636 eq678679
    | exact resolve eq678679 eq4945636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678679 eq4945636
  have eq4946417 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1091872 eq4946027
    | exact resolve eq4946027 eq1091872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091872 eq4946027
  have eq4946686 : False := by grind
  exact eq4946686

/-- `Equation4454`: `x ◇ (y ◇ x) = (z ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pyx_y_pxx_pxx_pxy_Equation4454 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4454 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4454.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) X2) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq22 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq10
    | exact resolve eq10 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq1960 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22
    | exact resolve eq22 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq2003 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1960 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1960
    | (have j0 := eq1960 X0 X1
       grind)
    | exact resolve eq1960 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960
  have eq2079 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq2003 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq2003 X0 X1
       grind)
    | exact superpose eq2003 eq12
    | (have j1 := eq2003 X1 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq2003 X0 X0
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq2003 X0 X1
       grind)
    | exact resolve eq12 eq2003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2003
  have eq2083 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2079 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2079
  have eq2163 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq2083 X0 X1
       grind)
    | exact superpose eq2083 eq10
    | (have j1 := eq2083 X0 X1
       grind)
    | exact resolve eq10 eq2083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2083
  have eq2320 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2163 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2163
    | (have j0 := eq2163 X0 X1
       grind)
    | exact resolve eq2163 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2163
  have eq2423 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2320 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq2320 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq2320
    | (have j0 := eq2320 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | exact resolve eq2320 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2516 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq2320 X0 X1
       grind)
    | exact superpose eq2320 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq2320 X0 X1
       grind)
    | exact resolve eq12 eq2320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2320
  have eq2588 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2423 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2423
  have eq2685 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2588 X0 X1
       have j1 := eq2516 X0 X1
       grind)
    | (have r₁ := eq2588 X0 X1
       have r₂ := eq2516 X0 X1
       grind)
    | (have r₁ := eq2588 X0 X0
       have r₂ := eq2516 X0 X1
       grind)
    | exact resolve eq2588 eq2516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2516 eq2588
  have eq5713 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2685 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2685
  have eq5725 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5713 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq5713 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq5713 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq5713 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5713
  have eq5793 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq5725 X0 (σ X1)
       grind)
    | exact superpose eq5725 eq30
    | (have j1 := eq5725 X0 (σ X1)
       grind)
    | exact resolve eq30 eq5725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5818 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq5725 (σ X0) (σ X1)
       grind)
    | exact superpose eq5725 eq15
    | (have j1 := eq5725 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq5725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5828 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq5725 (τ X0) X1
       grind)
    | exact superpose eq5725 eq18
    | (have j1 := eq5725 (τ X0) X1
       grind)
    | exact resolve eq18 eq5725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5841 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq5725 (τ X0) (τ X1)
       grind)
    | exact superpose eq5725 eq35
    | (have j1 := eq5725 (τ X0) (τ X1)
       grind)
    | exact resolve eq35 eq5725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6164 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5828 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5828
    | exact resolve eq5828 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5828
  have eq6239 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6164 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6164
    | (have j0 := eq6164 X0 X1
       grind)
    | exact resolve eq6164 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6164
  have eq6675 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5818 x y
       grind)
    | exact superpose eq5818 eq16
    | (have j1 := eq5818 x y
       grind)
    | exact resolve eq16 eq5818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6707 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq5818 X1 X0
       grind)
    | exact superpose eq5818 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq5818 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq5818 X0 X1
       grind)
    | exact resolve eq13 eq5818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6713 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq5818 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5818
  have eq6714 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq6707 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6707
  have eq6730 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq6714 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq6714 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq6714 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq6714 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6714
  have eq6745 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6730 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq6730
    | (have j0 := eq6730 X0 X1
       grind)
    | exact resolve eq6730 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6730
  have eq6753 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq6675
       have i₂ := eq6239 x y
       grind)
    | exact superpose eq6239 eq6675
    | (have j1 := eq6239 (σ x) (σ y)
       grind)
    | (have r₁ := eq6675
       have r₂ := eq6239 x y
       grind)
    | exact resolve eq6675 eq6239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6758 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq6753
  have eq6766 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq5793 (σ y) x
       have i₂ := eq6758
       grind)
    | exact superpose eq6758 eq5793
    | (have j0 := eq5793 (σ y) x
       grind)
    | exact resolve eq5793 eq6758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5793
  have eq6767 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) (σ y) X0
       have i₂ := eq6758
       grind)
    | exact superpose eq6758 eq9
    | exact resolve eq9 eq6758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6769 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq6758
       grind)
    | exact superpose eq6758 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq6758
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq6758
       grind)
    | exact resolve eq13 eq6758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6770 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq6769
  have eq6771 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq6770
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq6770 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6770
  have eq6772 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq6766
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq6766
    | exact resolve eq6766 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6766
  have eq6774 : (M.op (σ x) (σ x)) = (σ (k x y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq6771
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq6771
    | exact resolve eq6771 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6771
  have eq6796 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12 (σ x) (σ x)
       have i₂ := eq6774
       grind)
    | exact superpose eq6774 eq12
    | exact resolve eq12 eq6774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6797 : (σ (k x y)) = (k (σ x) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq6796
  have eq6798 : (σ (k x y)) = (σ (k x x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq6797
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq6797
    | exact resolve eq6797 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6797
  have eq6816 : (k x y) = (τ (σ (k x x))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq6798
       grind)
    | exact superpose eq6798 eq10
    | exact resolve eq10 eq6798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6798
  have eq6870 : (k x y) = (k x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq6816
       have i₂ := eq10 (k x x)
       grind)
    | exact superpose eq10 eq6816
    | exact resolve eq6816 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6816
  have eq6883 : (M.op x y) = (k x x) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq5725 x y
       have i₂ := eq6870
       grind)
    | exact superpose eq6870 eq5725
    | (have j0 := eq5725 x y
       grind)
    | exact resolve eq5725 eq6870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6870
  have eq6888 : (M.op x y) = (k x x) ∨ y = (M.op y x) := by grind
  clear eq6883
  have eq7365 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X0 (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6713 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq6713
    | exact resolve eq6713 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6713
  have eq7384 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k X0 (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7365 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7365
    | (have j0 := eq7365 X0
       grind)
    | exact resolve eq7365 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7365
  have eq7403 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq7384 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7384
    | (have j0 := eq7384 X0
       grind)
    | exact resolve eq7384 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7384
  have eq7458 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq7403 x
       have i₂ := eq6888
       grind)
    | exact superpose eq6888 eq7403
    | exact resolve eq7403 eq6888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6888 eq7403
  have eq7481 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq6767 (σ y)
       have i₂ := eq6758
       grind)
    | exact superpose eq6758 eq6767
    | exact resolve eq6767 eq6758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7484 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) X0 x
       have i₂ := eq6767 x
       grind)
    | exact superpose eq6767 eq9
    | exact resolve eq9 eq6767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7485 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 (σ x)) X1
       have i₂ := eq6767 X0
       grind)
    | exact superpose eq6767 eq9
    | exact resolve eq9 eq6767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7493 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq7481
  have eq7516 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12 (σ y) (σ y)
       have i₂ := eq7493
       grind)
    | exact superpose eq7493 eq12
    | exact resolve eq12 eq7493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7493
  have eq7517 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq7516
  have eq7518 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq7517
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq7517
    | exact resolve eq7517 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7517
  have eq7526 : (σ (M.op x y)) ≠ (σ (k y y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7518
       grind)
    | exact superpose eq7518 eq16
    | exact resolve eq16 eq7518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10322 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6772
       grind)
    | exact superpose eq6772 eq16
    | exact resolve eq16 eq6772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11118 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq7484 (M.op (σ x) (σ x))
       have i₂ := eq6767 (σ x)
       grind)
    | exact superpose eq6767 eq7484
    | exact resolve eq7484 eq6767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6767 eq7484
  have eq11143 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by grind
  clear eq11118
  have eq11186 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (σ (k y y))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq7485 X1 X0
       have i₂ := eq7518
       grind)
    | exact superpose eq7518 eq7485
    | exact resolve eq7485 eq7518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7485
  have eq11260 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (σ (k y y))) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have j0 := eq11186 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11186
  have eq23865 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11143
       have i₂ := eq6772
       grind)
    | exact superpose eq6772 eq11143
    | exact resolve eq11143 eq6772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6772
  have eq23866 : (σ (k y y)) = (M.op (σ x) (σ (k y y))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11143
       have i₂ := eq7518
       grind)
    | exact superpose eq7518 eq11143
    | exact resolve eq11143 eq7518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7518 eq11143
  have eq23940 : (σ (k y y)) = (M.op (σ x) (σ (k y y))) ∨ y = (M.op y x) := by grind
  clear eq23866
  have eq23941 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (k y x) := by grind
  clear eq23865
  have eq23982 : ∀ X0 : G, (M.op (M.op X0 (σ x)) X0) = (σ (k y y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq11260 X0 (σ x)
       have i₂ := eq23940
       grind)
    | exact superpose eq23940 eq11260
    | exact resolve eq11260 eq23940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11260 eq23940
  have eq24032 : ∀ X0 : G, (M.op (M.op X0 (σ x)) X0) = (σ (k y y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq23982 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23982
  have eq25425 : (σ x) = (σ (k x y)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq6774
       have i₂ := eq23941
       grind)
    | exact superpose eq23941 eq6774
    | exact resolve eq6774 eq23941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6774 eq23941
  have eq25485 : (σ x) = (σ (k x y)) ∨ y = (M.op y x) ∨ y = (k y x) := by grind
  clear eq25425
  have eq25514 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq6239 x y
       have i₂ := eq25485
       grind)
    | exact superpose eq25485 eq6239
    | (have j0 := eq6239 x y
       grind)
    | exact resolve eq6239 eq25485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6239 eq25485
  have eq25558 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ y = (k y x) := by grind
  clear eq25514
  have eq25601 : y = (k y x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq25558
       have r₂ := eq10322
       grind)
    | exact resolve eq25558 eq10322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10322 eq25558
  have eq25620 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq5725 y x
       have i₂ := eq25601
       grind)
    | exact superpose eq25601 eq5725
    | (have j0 := eq5725 x y
       grind)
    | exact resolve eq5725 eq25601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25637 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq25620
  have eq25649 : y ≠ y ∨ (M.op x y) = (M.op x x) ∨ (k x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq25637
       grind)
    | exact superpose eq25637 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq25637
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq25637
       grind)
    | exact resolve eq13 eq25637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25637
  have eq25650 : (M.op x y) = (M.op x x) ∨ (k x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq25649
  have eq25651 : (k x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq25650
       have r₂ := eq12 x y
       grind)
    | exact resolve eq25650 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25650
  have eq25689 : (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5725 x y
       have i₂ := eq25651
       grind)
    | exact superpose eq25651 eq5725
    | (have j0 := eq5725 x y
       grind)
    | exact resolve eq5725 eq25651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5725 eq25651
  have eq25708 : y = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq25689
       have r₂ := eq7458
       grind)
    | exact resolve eq25689 eq7458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7458 eq25689
  have eq25720 : y ≠ y ∨ (M.op x y) = (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq25708
       grind)
    | exact superpose eq25708 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq25708
       grind)
    | exact resolve eq13 eq25708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25708
  have eq25721 : y ≠ y ∨ (M.op x y) = (M.op x x) ∨ (k x y) = (M.op x x) := by grind
  clear eq25720
  have eq25722 : (M.op x y) = (M.op x x) ∨ (k x y) = (M.op x x) := by grind
  clear eq25721
  have eq25723 : (k x y) = (M.op x x) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq25722
       have r₂ := eq12 x y
       grind)
    | exact resolve eq25722 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25722
  have eq25735 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq6675
       have i₂ := eq25723
       grind)
    | exact superpose eq25723 eq6675
    | exact resolve eq6675 eq25723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6675 eq25723
  have eq2519858 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ (k (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6745 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6745
    | exact resolve eq6745 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2519859 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq6745 X1 X0
       grind)
    | exact superpose eq6745 eq10
    | (have j1 := eq6745 X1 X0
       grind)
    | exact resolve eq10 eq6745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2519862 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6745 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6745
  have eq2519863 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2519862 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2519862
  have eq2521504 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (k X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2519859 X0 X1
       have i₂ := eq2519863 X0
       grind)
    | exact superpose eq2519863 eq2519859
    | (have j0 := eq2519859 X0 X1
       grind)
    | exact resolve eq2519859 eq2519863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2519859
  have eq2521505 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ (k (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2519858 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq2519858
    | (have j0 := eq2519858 X0 X1
       grind)
    | exact resolve eq2519858 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2519858
  have eq2521606 : ∀ X0 X1 : G, (k X0 X1) = (k X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2521504 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq2521504
    | (have j0 := eq2521504 X0 X1
       grind)
    | exact resolve eq2521504 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2521504
  have eq2521607 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2521505 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq2521505
    | (have j0 := eq2521505 X0 X1
       grind)
    | exact resolve eq2521505 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2521505
  have eq2521610 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2519863 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2519863
    | exact resolve eq2519863 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2521845 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) X1) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq2519863 X0
       grind)
    | exact superpose eq2519863 eq9
    | exact resolve eq9 eq2519863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2522546 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2521610 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2521610
    | exact resolve eq2521610 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2521610
  have eq2522607 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2522546 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2522546
    | exact resolve eq2522546 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2522546
  have eq2524882 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2519863 X0
       have i₂ := eq2522607 X0
       grind)
    | exact superpose eq2522607 eq2519863
    | exact resolve eq2519863 eq2522607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2519863
  have eq2524927 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2521606 X0 X1
       have i₂ := eq2522607 X0
       grind)
    | exact superpose eq2522607 eq2521606
    | (have j0 := eq2521606 X0 X1
       grind)
    | exact resolve eq2521606 eq2522607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2521606
  have eq2524930 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) X1) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2521845 X0 X1
       have i₂ := eq2522607 X0
       grind)
    | exact superpose eq2522607 eq2521845
    | exact resolve eq2521845 eq2522607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2521845
  have eq2526671 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq7526
       have i₂ := eq2522607 y
       grind)
    | exact superpose eq2522607 eq7526
    | exact resolve eq7526 eq2522607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7526
  have eq2526836 : ∀ X0 : G, (M.op (M.op X0 (σ x)) X0) = (σ (M.op y y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq24032 X0
       have i₂ := eq2522607 y
       grind)
    | exact superpose eq2522607 eq24032
    | exact resolve eq24032 eq2522607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24032
  have eq2527831 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq2522607 (τ X0)
       grind)
    | exact superpose eq2522607 eq35
    | exact resolve eq35 eq2522607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq2527855 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2527831 X0
       have i₂ := eq2522607 X0
       grind)
    | exact superpose eq2522607 eq2527831
    | exact resolve eq2527831 eq2522607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2522607 eq2527831
  have eq2529690 : ∀ X0 X1 : G, (M.op (M.op X1 (τ X0)) X1) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) (τ X0) X1
       have i₂ := eq2527855 X0
       grind)
    | exact superpose eq2527855 eq9
    | exact resolve eq9 eq2527855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2530382 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2524930 X0 (σ X0)
       have i₂ := eq2524882 X0
       grind)
    | exact superpose eq2524882 eq2524930
    | exact resolve eq2524930 eq2524882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2530945 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ X1)) X0) = (M.op (M.op X2 (σ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2524930 X1 X0
       have i₂ := eq2524930 X1 X2
       grind)
    | exact superpose eq2524930 eq2524930
    | exact resolve eq2524930 eq2524930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2532990 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X2) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2530945 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2530945
    | exact resolve eq2530945 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2535461 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) X3) = (M.op X2 (M.op (M.op X0 (σ X1)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X2 (σ X1)) X3
       have i₂ := eq2530945 X2 X1 X0
       grind)
    | (have i₁ := eq9 X2 (M.op X2 (σ X1)) X3
       have i₂ := eq2530945 X0 X1 X2
       grind)
    | exact superpose eq2530945 eq9
    | exact resolve eq9 eq2530945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2530945
  have eq2538073 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op X2 (M.op X3 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2532990 (M.op X3 X1) X1 X2
       have i₂ := eq9 X1 X3 X0
       grind)
    | exact superpose eq9 eq2532990
    | exact resolve eq2532990 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2538190 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op (M.op X0 X1) X0) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2532990 X3 (M.op X3 X1) X2
       have i₂ := eq2532990 X1 X0 X3
       grind)
    | (have i₁ := eq2532990 X3 (M.op X3 X1) X2
       have i₂ := eq2532990 X1 X3 X0
       grind)
    | exact superpose eq2532990 eq2532990
    | exact resolve eq2532990 eq2532990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2544488 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) X3) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X2 X1) X3
       have i₂ := eq2532990 X1 X0 X2
       grind)
    | (have i₁ := eq9 X2 (M.op X2 X1) X3
       have i₂ := eq2532990 X1 X2 X0
       grind)
    | exact superpose eq2532990 eq9
    | exact resolve eq9 eq2532990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2547231 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op X3 (M.op (M.op (M.op X0 X1) X0) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2544488 X1 (M.op (M.op x x) x) X3 X2
       have i₂ := eq2544488 x x X1 X0
       grind)
    | exact superpose eq2544488 eq2544488
    | exact resolve eq2544488 eq2544488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2548280 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op X3 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2544488 x X0 X3 X2
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq2544488
    | exact resolve eq2544488 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2550370 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X1)) = (M.op X0 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X3 x
       have i₂ := eq2544488 X1 X2 X0 x
       grind)
    | exact superpose eq2544488 eq9
    | exact resolve eq9 eq2544488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2551253 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X3) X4) = (M.op X3 (M.op X0 (M.op (M.op X1 X2) X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X3 (M.op X3 X0) X4
       have i₂ := eq2544488 X1 X2 X0 X3
       grind)
    | exact superpose eq2544488 eq9
    | exact resolve eq9 eq2544488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2558551 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 X1))) = (M.op X0 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X3 x
       have i₂ := eq2548280 X1 X2 x X0
       grind)
    | exact superpose eq2548280 eq9
    | exact resolve eq9 eq2548280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2558851 : ∀ X0 X1 X2 X4 X5 : G, (M.op X0 (M.op X1 (M.op X2 X1))) = (M.op X0 (M.op (M.op X4 X5) X4)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq2544488 X4 X5 X0 x
       have i₂ := eq2548280 X1 X2 x X0
       grind)
    | exact superpose eq2548280 eq2544488
    | exact resolve eq2544488 eq2548280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2544488
  have eq2558884 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op X1 (M.op X2 X1))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2524930 X0 x
       have i₂ := eq2548280 X1 X2 x (σ X0)
       grind)
    | exact superpose eq2548280 eq2524930
    | exact resolve eq2524930 eq2548280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2561256 : ∀ X0 X1 X2 X3 : G, (M.op (σ X3) (σ (M.op X3 X3))) = (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (σ X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2524930 X3 (M.op X1 (M.op X2 X1))
       have i₂ := eq2548280 X1 X2 X0 (M.op (M.op X1 (M.op X2 X1)) (σ X3))
       grind)
    | exact superpose eq2548280 eq2524930
    | exact resolve eq2524930 eq2548280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2524930
  have eq2564648 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X4 X0)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq2550370 X0 x x X4
       have i₂ := eq2550370 X0 x x X1
       grind)
    | (have i₁ := eq2550370 X0 X0 x x
       have i₂ := eq2550370 X0 X1 x (M.op X0 x)
       grind)
    | exact superpose eq2550370 eq2550370
    | exact resolve eq2550370 eq2550370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2582140 : ∀ X0 X1 X2 : G, (M.op (τ X0) (M.op X1 (M.op X2 X1))) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2558551 (τ X0) X1 X2 (τ X0)
       have i₂ := eq2527855 X0
       grind)
    | exact superpose eq2527855 eq2558551
    | exact resolve eq2558551 eq2527855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2586729 : ∀ X0 X1 X2 X3 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (M.op (M.op X1 (M.op (M.op X2 (M.op X3 X2)) (τ X0))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2548280 X2 X3 X1 (M.op (M.op X2 (M.op X3 X2)) (τ X0))
       have i₂ := eq2529690 X0 (M.op X2 (M.op X3 X2))
       grind)
    | exact superpose eq2529690 eq2548280
    | exact resolve eq2548280 eq2529690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2529690
  have eq2597125 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 (M.op X1 X2)) X0) = (M.op (M.op X4 (M.op X5 X2)) X4) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq2538073 x X2 X4 X5
       have i₂ := eq2538073 x X2 X0 X1
       grind)
    | exact superpose eq2538073 eq2538073
    | exact resolve eq2538073 eq2538073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2597907 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op (M.op X2 X3) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2538073 X0 X1 X3 (M.op X1 (σ x))
       have i₂ := eq2535461 X1 x X3 X2
       grind)
    | exact superpose eq2535461 eq2538073
    | exact resolve eq2538073 eq2535461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2535461 eq2538073
  have eq2631940 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) X4) = (M.op (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X3) X2)) X1)) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2538190 X1 (M.op (M.op X2 X3) X2) X4 X5
       have i₂ := eq2551253 X5 X2 X3 (M.op (M.op X1 (M.op (M.op X2 X3) X2)) X1) X0
       grind)
    | exact superpose eq2551253 eq2538190
    | exact resolve eq2538190 eq2551253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2538190 eq2551253
  have eq2635532 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op (M.op X2 (M.op X3 X4)) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2597125 X2 X3 X4 X0 (M.op X4 x)
       have i₂ := eq2550370 X0 X4 x X1
       grind)
    | (have i₁ := eq2597125 X0 X1 X0 X0 X3
       have i₂ := eq2550370 X0 X1 X2 X3
       grind)
    | exact superpose eq2550370 eq2597125
    | exact resolve eq2597125 eq2550370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2550370
  have eq2635588 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X0) X1) = (M.op (M.op X2 (M.op X3 X4)) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2597125 X2 X3 X4 X1 (M.op (M.op x X4) x)
       have i₂ := eq2547231 x X4 X0 X1
       grind)
    | exact superpose eq2547231 eq2597125
    | exact resolve eq2597125 eq2547231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2597125
  have eq2699170 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 X2)) X0) = (M.op (M.op X3 (M.op X4 X5)) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2532990 (M.op X1 X2) X2 X0
       have i₂ := eq2635532 X2 X1 X3 X4 X5
       grind)
    | (have i₁ := eq2532990 (M.op X3 X4) X2 X2
       have i₂ := eq2635532 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq2635532 eq2532990
    | exact resolve eq2532990 eq2635532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2699193 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op X3 X4) X3) X4) = (M.op (M.op (M.op X0 (M.op X1 X2)) X0) (M.op X6 X5)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq2597907 X3 X4 X5 (M.op X6 X5)
       have i₂ := eq2635532 X5 X6 X0 X1 X2
       grind)
    | (have i₁ := eq2597907 X0 X1 X2 (M.op X3 X4)
       have i₂ := eq2635532 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq2635532 eq2597907
    | exact resolve eq2597907 eq2635532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2597907
  have eq2699399 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 X3)) = (M.op (M.op (M.op X0 (M.op X1 X2)) X0) (M.op X3 (M.op X5 X3))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq9 X3 X4 (M.op X3 (M.op X5 X3))
       have i₂ := eq2635532 X3 X5 X0 X1 X2
       grind)
    | (have i₁ := eq9 X2 X1 (M.op X2 (M.op X3 X4))
       have i₂ := eq2635532 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq2635532 eq9
    | exact resolve eq9 eq2635532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2699454 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X5 X3) X5) = (M.op (M.op (M.op X0 (M.op X1 X2)) X0) (M.op X3 (M.op X4 X3))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2532990 X3 X5 (M.op X3 (M.op X4 X3))
       have i₂ := eq2635532 X3 X4 X0 X1 X2
       grind)
    | (have i₁ := eq2532990 X2 X1 (M.op X2 (M.op X3 X4))
       have i₂ := eq2635532 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq2635532 eq2532990
    | exact resolve eq2532990 eq2635532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2635532
  have eq2704118 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X1) X2) = (M.op (M.op X3 (τ (M.op X0 X0))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2635588 X1 X2 X3 (τ X0) (τ X0)
       have i₂ := eq2527855 X0
       grind)
    | exact superpose eq2527855 eq2635588
    | exact resolve eq2635588 eq2527855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2742446 : ∀ X0 X1 X2 X4 X5 X6 X7 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) (M.op X4 X5)) = (M.op (M.op X6 (τ (M.op X7 X7))) X6) := by
    intro X0 X1 X2 X4 X5 X6 X7
    first
    | (have i₁ := eq2704118 X7 x (M.op X4 X5) X6
       have i₂ := eq2699170 x X4 X5 X0 X1 X2
       grind)
    | (have i₁ := eq2704118 X7 x (M.op X4 X5) X6
       have i₂ := eq2699170 X0 X1 X2 x X4 X5
       grind)
    | exact superpose eq2699170 eq2704118
    | exact resolve eq2704118 eq2699170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2699170 eq2704118
  have eq2754084 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2521607 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2521607
    | exact resolve eq2521607 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2521607
  have eq2754097 : y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2754084 x y
       have i₂ := eq25601
       grind)
    | exact superpose eq25601 eq2754084
    | exact resolve eq2754084 eq25601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25601
  have eq2754131 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq2754097
  have eq2754836 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2526671
       have i₂ := eq2754131
       grind)
    | exact superpose eq2754131 eq2526671
    | exact resolve eq2526671 eq2754131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2526671
  have eq2755067 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op y y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq2548280 y y X0 X1
       have i₂ := eq2754131
       grind)
    | exact superpose eq2754131 eq2548280
    | exact resolve eq2548280 eq2754131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2755073 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op y y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq2558551 X0 y y X1
       have i₂ := eq2754131
       grind)
    | exact superpose eq2754131 eq2558551
    | exact resolve eq2558551 eq2754131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2558551
  have eq2755081 : ∀ X0 : G, (M.op y y) = (M.op y (M.op X0 y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2564648 y X0 y
       have i₂ := eq2754131
       grind)
    | exact superpose eq2754131 eq2564648
    | exact resolve eq2564648 eq2754131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2755108 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y x) := by grind
  clear eq2754836
  have eq2756593 : (M.op y y) = (M.op y (σ (M.op y y))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2755081 (M.op y (σ x))
       have i₂ := eq2526836 y
       grind)
    | exact superpose eq2526836 eq2755081
    | exact resolve eq2755081 eq2526836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2755081
  have eq2757504 : (M.op y y) = (M.op y (σ (M.op y y))) ∨ y = (M.op y x) := by grind
  clear eq2756593
  have eq2757513 : y = (M.op y (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2757504
       have i₂ := eq2754131
       grind)
    | exact superpose eq2754131 eq2757504
    | exact resolve eq2757504 eq2754131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2757537 : y = (M.op y (σ y)) ∨ y = (M.op y x) := by grind
  clear eq2757513
  have eq2757639 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2532990 (σ y) X0 y
       have i₂ := eq2757537
       grind)
    | exact superpose eq2757537 eq2532990
    | exact resolve eq2532990 eq2757537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2757537
  have eq2759145 : (M.op y y) = (M.op (σ y) (M.op y y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2757639 x
       have i₂ := eq2755067 x (σ y)
       grind)
    | exact superpose eq2755067 eq2757639
    | exact resolve eq2757639 eq2755067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2755067 eq2757639
  have eq2759404 : (M.op y y) = (M.op (σ y) (M.op y y)) ∨ y = (M.op y x) := by grind
  clear eq2759145
  have eq2759410 : y = (M.op (σ y) y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2759404
       have i₂ := eq2754131
       grind)
    | exact superpose eq2754131 eq2759404
    | exact resolve eq2759404 eq2754131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2759404
  have eq2759496 : y = (M.op (σ y) y) ∨ y = (M.op y x) := by grind
  clear eq2759410
  have eq2762811 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq2755073 X0 X1
       have i₂ := eq2754131
       grind)
    | exact superpose eq2754131 eq2755073
    | exact resolve eq2755073 eq2754131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2755073
  have eq2763073 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 y) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have j0 := eq2762811 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2762811
  have eq2764292 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op X0 y) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq2547231 x X0 X1 X0
       have i₂ := eq2763073 X0 (M.op (M.op x X0) x)
       grind)
    | exact superpose eq2763073 eq2547231
    | exact resolve eq2547231 eq2763073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2765575 : (σ (M.op y y)) = (M.op (σ x) y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2526836 x
       have i₂ := eq2764292 (σ x) x
       grind)
    | exact superpose eq2764292 eq2526836
    | exact resolve eq2526836 eq2764292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2526836
  have eq2765950 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (M.op X0 y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq2763073 X1 (M.op X1 X0)
       have i₂ := eq2764292 X0 X1
       grind)
    | exact superpose eq2764292 eq2763073
    | exact resolve eq2763073 eq2764292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2763073
  have eq2766533 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (M.op X0 y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have j0 := eq2765950 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2765950
  have eq2766536 : (σ (M.op y y)) = (M.op (σ x) y) ∨ y = (M.op y x) := by grind
  clear eq2765575
  have eq2768512 : (σ y) = (M.op (σ x) y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2766536
       have i₂ := eq2754131
       grind)
    | exact superpose eq2754131 eq2766536
    | exact resolve eq2766536 eq2754131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2754131
  have eq2768532 : (σ y) = (M.op (σ x) y) ∨ y = (M.op y x) := by grind
  clear eq2768512
  have eq2768687 : (M.op (σ y) (σ x)) = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2764292 y (σ x)
       have i₂ := eq2768532
       grind)
    | exact superpose eq2768532 eq2764292
    | exact resolve eq2764292 eq2768532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2768532
  have eq2768688 : (M.op (σ y) (σ x)) = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq2768687
  have eq2768821 : (σ y) = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq6758
       have i₂ := eq2768688
       grind)
    | exact superpose eq2768688 eq6758
    | exact resolve eq6758 eq2768688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6758 eq2768688
  have eq2768848 : (σ y) = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq2768821
  have eq2769096 : (σ y) = (M.op y (σ (σ y))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2757504
       have i₂ := eq2768848
       grind)
    | exact superpose eq2768848 eq2757504
    | exact resolve eq2757504 eq2768848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2757504
  have eq2769100 : (σ (σ y)) = (M.op (σ x) y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2766536
       have i₂ := eq2768848
       grind)
    | exact superpose eq2768848 eq2766536
    | exact resolve eq2766536 eq2768848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2769349 : (σ y) = (M.op (σ y) y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2764292 y y
       have i₂ := eq2768848
       grind)
    | exact superpose eq2768848 eq2764292
    | exact resolve eq2764292 eq2768848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2768848
  have eq2769350 : (σ y) = (M.op (σ y) y) ∨ y = (M.op y x) := by grind
  clear eq2769349
  have eq2769364 : (σ (σ y)) = (M.op (σ x) y) ∨ y = (M.op y x) := by grind
  clear eq2769100
  have eq2769368 : (σ y) = (M.op y (σ (σ y))) ∨ y = (M.op y x) := by grind
  clear eq2769096
  have eq2771113 : (M.op (σ y) (σ y)) = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2764292 y (σ y)
       have i₂ := eq2769350
       grind)
    | exact superpose eq2769350 eq2764292
    | exact resolve eq2764292 eq2769350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2769350
  have eq2771114 : (M.op (σ y) (σ y)) = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq2771113
  have eq2771127 : (M.op y y) = (σ (M.op y y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2771114
       have i₂ := eq2524882 y
       grind)
    | exact superpose eq2524882 eq2771114
    | exact resolve eq2771114 eq2524882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2771114
  have eq2777721 : (M.op y y) = (M.op (σ x) y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2766536
       have i₂ := eq2771127
       grind)
    | exact superpose eq2771127 eq2766536
    | exact resolve eq2766536 eq2771127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2766536 eq2771127
  have eq2777741 : (M.op y y) = (M.op (σ x) y) ∨ y = (M.op y x) := by grind
  clear eq2777721
  have eq2786800 : (M.op y y) = (σ (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2769364
       have i₂ := eq2777741
       grind)
    | exact superpose eq2777741 eq2769364
    | exact resolve eq2769364 eq2777741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2769364 eq2777741
  have eq2786857 : (M.op y y) = (σ (σ y)) ∨ y = (M.op y x) := by grind
  clear eq2786800
  have eq2786862 : (σ y) = (M.op y (M.op y y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2769368
       have i₂ := eq2786857
       grind)
    | exact superpose eq2786857 eq2769368
    | exact resolve eq2769368 eq2786857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2769368 eq2786857
  have eq2786873 : (σ y) = (M.op y (M.op y y)) ∨ y = (M.op y x) := by grind
  clear eq2786862
  have eq2792594 : ∀ X0 : G, (σ y) = (M.op y (M.op X0 y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2564648 y X0 y
       have i₂ := eq2786873
       grind)
    | exact superpose eq2786873 eq2564648
    | exact resolve eq2564648 eq2786873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2786873
  have eq2796251 : ∀ X0 : G, (σ y) = (M.op (M.op X0 y) X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2547231 x y X0 y
       have i₂ := eq2792594 (M.op (M.op x y) x)
       grind)
    | exact superpose eq2792594 eq2547231
    | exact resolve eq2547231 eq2792594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2547231 eq2792594
  have eq2798746 : ∀ X0 : G, (M.op X0 y) = (M.op (σ y) (M.op X0 y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2764292 X0 (M.op X0 y)
       have i₂ := eq2796251 X0
       grind)
    | exact superpose eq2796251 eq2764292
    | exact resolve eq2764292 eq2796251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2764292 eq2796251
  have eq2799684 : ∀ X0 : G, (M.op X0 y) = (M.op (σ y) (M.op X0 y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq2798746 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2798746
  have eq2928085 : ∀ X0 : G, (M.op X0 y) = (M.op (σ y) y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2766533 X0 (σ y)
       have i₂ := eq2799684 X0
       grind)
    | exact superpose eq2799684 eq2766533
    | exact resolve eq2766533 eq2799684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2766533 eq2799684
  have eq2928200 : ∀ X0 : G, (M.op X0 y) = (M.op (σ y) y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq2928085 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2928085
  have eq2929167 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2759496
       have i₂ := eq2928200 X0
       grind)
    | (have i₁ := eq2759496
       have i₂ := eq2928200 (σ y)
       grind)
    | exact superpose eq2928200 eq2759496
    | exact resolve eq2759496 eq2928200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2759496 eq2928200
  have eq2929279 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq2929167 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2929167
  have eq2933321 : (σ y) ≠ (σ y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2755108
       have i₂ := eq2929279 x
       grind)
    | exact superpose eq2929279 eq2755108
    | exact resolve eq2755108 eq2929279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2755108 eq2929279
  have eq2934403 : (σ y) ≠ (σ y) ∨ y = (M.op y x) := by grind
  clear eq2933321
  have eq2934404 : y = (M.op y x) := by grind
  clear eq2934403
  have eq2935375 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 y
       have i₂ := eq2934404
       grind)
    | exact superpose eq2934404 eq9
    | exact resolve eq9 eq2934404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2935872 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 x) X0) := by
    intro X0
    first
    | (have i₁ := eq2532990 x X0 y
       have i₂ := eq2934404
       grind)
    | exact superpose eq2934404 eq2532990
    | exact resolve eq2532990 eq2934404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2532990
  have eq2935885 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2548280 x y X0 X1
       have i₂ := eq2934404
       grind)
    | exact superpose eq2934404 eq2548280
    | exact resolve eq2548280 eq2934404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2548280
  have eq2935892 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X1))) = (M.op X0 (M.op y y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2558851 X0 X1 X2 y x
       have i₂ := eq2934404
       grind)
    | exact superpose eq2934404 eq2558851
    | exact resolve eq2558851 eq2934404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2558851
  have eq2935893 : ∀ X0 : G, (M.op (σ X0) (M.op x y)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2558884 X0 x y
       have i₂ := eq2934404
       grind)
    | exact superpose eq2934404 eq2558884
    | exact resolve eq2558884 eq2934404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2558884
  have eq2935899 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq2564648 x X0 y
       have i₂ := eq2934404
       grind)
    | exact superpose eq2934404 eq2564648
    | exact resolve eq2564648 eq2934404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2564648
  have eq2935903 : ∀ X0 : G, (M.op (τ X0) (M.op x y)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2582140 X0 x y
       have i₂ := eq2934404
       grind)
    | exact superpose eq2934404 eq2582140
    | exact resolve eq2582140 eq2934404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2582140
  have eq2935915 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X0) = (M.op (M.op y y) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2635588 y x X0 X1 X2
       have i₂ := eq2934404
       grind)
    | exact superpose eq2934404 eq2635588
    | exact resolve eq2635588 eq2934404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2635588
  have eq2936210 : ∀ X0 X4 X5 : G, (M.op (M.op X4 X5) X4) = (M.op (M.op X0 (M.op (M.op y y) x)) X0) := by
    intro X0 X4 X5
    first
    | (have i₁ := eq2631940 X0 x x x X4 X5
       have i₂ := eq2935915 x (M.op x x) x
       grind)
    | exact superpose eq2935915 eq2631940
    | exact resolve eq2631940 eq2935915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2631940
  have eq2936415 : ∀ X3 X4 X5 X6 : G, (M.op (M.op (M.op X3 X4) X3) X4) = (M.op (M.op (M.op y y) x) (M.op X6 X5)) := by
    intro X3 X4 X5 X6
    first
    | (have i₁ := eq2699193 x x x X3 X4 X5 X6
       have i₂ := eq2935915 x x x
       grind)
    | exact superpose eq2935915 eq2699193
    | exact resolve eq2699193 eq2935915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2699193
  have eq2936416 : ∀ X3 X4 X5 : G, (M.op X3 (M.op X4 X3)) = (M.op (M.op (M.op y y) x) (M.op X3 (M.op X5 X3))) := by
    intro X3 X4 X5
    first
    | (have i₁ := eq2699399 x x x X3 X4 X5
       have i₂ := eq2935915 x x x
       grind)
    | exact superpose eq2935915 eq2699399
    | exact resolve eq2699399 eq2935915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2699399
  have eq2936417 : ∀ X3 X4 X5 : G, (M.op (M.op X5 X3) X5) = (M.op (M.op (M.op y y) x) (M.op X3 (M.op X4 X3))) := by
    intro X3 X4 X5
    first
    | (have i₁ := eq2699454 x x x X3 X4 X5
       have i₂ := eq2935915 x x x
       grind)
    | exact superpose eq2935915 eq2699454
    | exact resolve eq2699454 eq2935915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2699454
  have eq2936430 : ∀ X4 X5 X6 X7 : G, (M.op (M.op (M.op y y) x) (M.op X4 X5)) = (M.op (M.op X6 (τ (M.op X7 X7))) X6) := by
    intro X4 X5 X6 X7
    first
    | (have i₁ := eq2742446 x x x X4 X5 X6 X7
       have i₂ := eq2935915 x x x
       grind)
    | exact superpose eq2935915 eq2742446
    | exact resolve eq2742446 eq2935915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2742446
  have eq2936772 : ∀ X3 : G, (M.op (M.op y y) x) = (M.op (σ X3) (σ (M.op X3 X3))) := by
    intro X3
    first
    | (have i₁ := eq2561256 x x x X3
       have i₂ := eq2935915 x (M.op x (M.op x x)) (σ X3)
       grind)
    | exact superpose eq2935915 eq2561256
    | exact resolve eq2561256 eq2935915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2561256
  have eq2936776 : ∀ X0 : G, (M.op (M.op y y) x) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2586729 X0 x x x
       have i₂ := eq2935915 x (M.op x (M.op x x)) (τ X0)
       grind)
    | exact superpose eq2935915 eq2586729
    | exact resolve eq2586729 eq2935915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2586729 eq2935915
  have eq2938936 : ∀ X0 : G, (M.op (σ X0) (M.op x y)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2530382 X0
       have i₂ := eq2935893 X0
       grind)
    | exact superpose eq2935893 eq2530382
    | exact resolve eq2530382 eq2935893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2530382
  have eq2944863 : (M.op y y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq2935872 x
       have i₂ := eq2935885 x x
       grind)
    | exact superpose eq2935885 eq2935872
    | exact resolve eq2935872 eq2935885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2935872
  have eq2944907 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2935375 x
       have i₂ := eq2935899 x
       grind)
    | exact superpose eq2935899 eq2935375
    | exact resolve eq2935375 eq2935899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2935375 eq2935899
  have eq2944991 : ∀ X0 : G, (M.op (M.op y y) x) = (M.op (τ X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2936776 X0
       have i₂ := eq2935903 X0
       grind)
    | exact superpose eq2935903 eq2936776
    | exact resolve eq2936776 eq2935903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2935903 eq2936776
  have eq2944995 : ∀ X3 : G, (M.op (M.op y y) x) = (M.op (σ X3) (M.op x y)) := by
    intro X3
    first
    | (have i₁ := eq2936772 X3
       have i₂ := eq2935893 X3
       grind)
    | exact superpose eq2935893 eq2936772
    | exact resolve eq2936772 eq2935893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2935893 eq2936772
  have eq2945089 : ∀ X4 X5 X7 : G, (M.op (M.op (M.op y y) x) (M.op X4 X5)) = (M.op (τ (M.op X7 X7)) (M.op x y)) := by
    intro X4 X5 X7
    first
    | (have i₁ := eq2936430 X4 X5 x X7
       have i₂ := eq2935885 x (τ (M.op X7 X7))
       grind)
    | exact superpose eq2935885 eq2936430
    | exact resolve eq2936430 eq2935885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2936430
  have eq2945102 : ∀ X3 X5 : G, (M.op (M.op (M.op y y) x) (M.op y y)) = (M.op (M.op X5 X3) X5) := by
    intro X3 X5
    first
    | (have i₁ := eq2936417 X3 x X5
       have i₂ := eq2935892 (M.op (M.op y y) x) X3 x
       grind)
    | exact superpose eq2935892 eq2936417
    | exact resolve eq2936417 eq2935892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2936417
  have eq2945103 : ∀ X3 X4 : G, (M.op X3 (M.op X4 X3)) = (M.op (M.op (M.op y y) x) (M.op y y)) := by
    intro X3 X4
    first
    | (have i₁ := eq2936416 X3 X4 x
       have i₂ := eq2935892 (M.op (M.op y y) x) X3 x
       grind)
    | exact superpose eq2935892 eq2936416
    | exact resolve eq2936416 eq2935892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2935892 eq2936416
  have eq2945104 : ∀ X4 X5 X6 : G, (M.op (M.op X4 (M.op x y)) X4) = (M.op (M.op (M.op y y) x) (M.op X6 X5)) := by
    intro X4 X5 X6
    first
    | (have i₁ := eq2936415 x X4 X5 X6
       have i₂ := eq2935885 x X4
       grind)
    | exact superpose eq2935885 eq2936415
    | exact resolve eq2936415 eq2935885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2936415
  have eq2945230 : ∀ X4 X5 : G, (M.op (M.op X4 X5) X4) = (M.op (M.op (M.op y y) x) (M.op x y)) := by
    intro X4 X5
    first
    | (have i₁ := eq2936210 x X4 X5
       have i₂ := eq2935885 x (M.op (M.op y y) x)
       grind)
    | exact superpose eq2935885 eq2936210
    | exact resolve eq2936210 eq2935885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2936210
  have eq2954268 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq2944863
       have i₂ := eq2944907
       grind)
    | exact superpose eq2944907 eq2944863
    | exact resolve eq2944863 eq2944907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2944863
  have eq2954344 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (τ X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2944991 X0
       have i₂ := eq2944907
       grind)
    | exact superpose eq2944907 eq2944991
    | exact resolve eq2944991 eq2944907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2944991
  have eq2954348 : ∀ X3 : G, (M.op (M.op x y) x) = (M.op (σ X3) (M.op x y)) := by
    intro X3
    first
    | (have i₁ := eq2944995 X3
       have i₂ := eq2944907
       grind)
    | exact superpose eq2944907 eq2944995
    | exact resolve eq2944995 eq2944907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2944995
  have eq2954442 : ∀ X4 X5 X7 : G, (M.op (τ (M.op X7 X7)) (M.op x y)) = (M.op (M.op (M.op x y) x) (M.op X4 X5)) := by
    intro X4 X5 X7
    first
    | (have i₁ := eq2945089 X4 X5 X7
       have i₂ := eq2944907
       grind)
    | exact superpose eq2944907 eq2945089
    | exact resolve eq2945089 eq2944907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2945089
  have eq2954455 : ∀ X3 : G, (M.op (M.op (M.op y y) x) (M.op y y)) = (M.op X3 (M.op x y)) := by
    intro X3
    first
    | (have i₁ := eq2945102 X3 x
       have i₂ := eq2935885 x X3
       grind)
    | exact superpose eq2935885 eq2945102
    | exact resolve eq2945102 eq2935885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2945102
  have eq2954456 : ∀ X3 X4 : G, (M.op X3 (M.op X4 X3)) = (M.op x (M.op x y)) := by
    intro X3 X4
    first
    | (have i₁ := eq2945103 X3 X4
       have i₂ := eq2935885 (M.op y y) x
       grind)
    | exact superpose eq2935885 eq2945103
    | exact resolve eq2945103 eq2935885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2945103
  have eq2954457 : ∀ X4 X5 X6 : G, (M.op (M.op X4 (M.op x y)) X4) = (M.op (M.op (M.op x y) x) (M.op X6 X5)) := by
    intro X4 X5 X6
    first
    | (have i₁ := eq2945104 X4 X5 X6
       have i₂ := eq2944907
       grind)
    | exact superpose eq2944907 eq2945104
    | exact resolve eq2945104 eq2944907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2945104
  have eq2954582 : ∀ X4 X5 : G, (M.op (M.op X4 X5) X4) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    intro X4 X5
    first
    | (have i₁ := eq2945230 X4 X5
       have i₂ := eq2944907
       grind)
    | exact superpose eq2944907 eq2945230
    | exact resolve eq2945230 eq2944907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2945230
  have eq2958781 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op (τ X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2954344 X0
       have i₂ := eq2935885 x y
       grind)
    | exact superpose eq2935885 eq2954344
    | exact resolve eq2954344 eq2935885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2954344
  have eq2958785 : ∀ X3 : G, (M.op y (M.op x y)) = (M.op (σ X3) (M.op x y)) := by
    intro X3
    first
    | (have i₁ := eq2954348 X3
       have i₂ := eq2935885 x y
       grind)
    | exact superpose eq2935885 eq2954348
    | exact resolve eq2954348 eq2935885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2954348
  have eq2958860 : ∀ X4 X5 X7 : G, (M.op (τ (M.op X7 X7)) (M.op x y)) = (M.op (M.op y (M.op x y)) (M.op X4 X5)) := by
    intro X4 X5 X7
    first
    | (have i₁ := eq2954442 X4 X5 X7
       have i₂ := eq2935885 x y
       grind)
    | exact superpose eq2935885 eq2954442
    | exact resolve eq2954442 eq2935885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2954442
  have eq2958872 : ∀ X3 : G, (M.op x (M.op x y)) = (M.op X3 (M.op x y)) := by
    intro X3
    first
    | (have i₁ := eq2954455 X3
       have i₂ := eq2935885 (M.op y y) x
       grind)
    | exact superpose eq2935885 eq2954455
    | exact resolve eq2954455 eq2935885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2954455
  have eq2958873 : ∀ X3 X4 : G, (M.op x y) = (M.op X3 (M.op X4 X3)) := by
    intro X3 X4
    first
    | (have i₁ := eq2954456 X3 X4
       have i₂ := eq2954268
       grind)
    | exact superpose eq2954268 eq2954456
    | exact resolve eq2954456 eq2954268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2954456
  have eq2958874 : ∀ X4 X5 X6 : G, (M.op (M.op X4 (M.op x y)) X4) = (M.op (M.op y (M.op x y)) (M.op X6 X5)) := by
    intro X4 X5 X6
    first
    | (have i₁ := eq2954457 X4 X5 X6
       have i₂ := eq2935885 x y
       grind)
    | exact superpose eq2935885 eq2954457
    | exact resolve eq2954457 eq2935885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2954457
  have eq2958957 : ∀ X4 X5 : G, (M.op (M.op X4 X5) X4) = (M.op x (M.op x y)) := by
    intro X4 X5
    first
    | (have i₁ := eq2954582 X4 X5
       have i₂ := eq2935885 (M.op x y) x
       grind)
    | exact superpose eq2935885 eq2954582
    | exact resolve eq2954582 eq2935885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2935885 eq2954582
  have eq2960411 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2938936 X0
       have i₂ := eq2958785 X0
       grind)
    | exact superpose eq2958785 eq2938936
    | exact resolve eq2938936 eq2958785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2938936 eq2958785
  have eq2960460 : ∀ X4 X5 : G, (M.op y (M.op x y)) = (M.op (M.op y (M.op x y)) (M.op X4 X5)) := by
    intro X4 X5
    first
    | (have i₁ := eq2958860 X4 X5 x
       have i₂ := eq2958781 (M.op x x)
       grind)
    | exact superpose eq2958781 eq2958860
    | exact resolve eq2958860 eq2958781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2958781 eq2958860
  have eq2960470 : ∀ X3 : G, (M.op x y) = (M.op X3 (M.op x y)) := by
    intro X3
    first
    | (have i₁ := eq2958872 X3
       have i₂ := eq2954268
       grind)
    | exact superpose eq2954268 eq2958872
    | exact resolve eq2958872 eq2954268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2958872
  have eq2961211 : ∀ X4 X5 X6 : G, (M.op (M.op X4 (M.op x y)) X4) = (M.op (M.op x y) (M.op X6 X5)) := by
    intro X4 X5 X6
    first
    | (have i₁ := eq2958874 X4 X5 X6
       have i₂ := eq2958873 y x
       grind)
    | exact superpose eq2958873 eq2958874
    | exact resolve eq2958874 eq2958873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2958874
  have eq2961280 : ∀ X4 X5 : G, (M.op x y) = (M.op (M.op X4 X5) X4) := by
    intro X4 X5
    first
    | (have i₁ := eq2958957 X4 X5
       have i₂ := eq2954268
       grind)
    | exact superpose eq2954268 eq2958957
    | exact resolve eq2958957 eq2954268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2954268 eq2958957
  have eq2962077 : ∀ X0 : G, (M.op x y) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2960411 X0
       have i₂ := eq2958873 y x
       grind)
    | exact superpose eq2958873 eq2960411
    | exact resolve eq2960411 eq2958873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2960411
  have eq2962103 : ∀ X4 X5 : G, (M.op x y) = (M.op (M.op x y) (M.op X4 X5)) := by
    intro X4 X5
    first
    | (have i₁ := eq2960460 X4 X5
       have i₂ := eq2958873 y x
       grind)
    | exact superpose eq2958873 eq2960460
    | exact resolve eq2960460 eq2958873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2960460
  have eq2962802 : ∀ X4 X5 X6 : G, (M.op (M.op x y) X4) = (M.op (M.op x y) (M.op X6 X5)) := by
    intro X4 X5 X6
    first
    | (have i₁ := eq2961211 X4 X5 X6
       have i₂ := eq2960470 X4
       grind)
    | exact superpose eq2960470 eq2961211
    | exact resolve eq2961211 eq2960470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2961211
  have eq2963499 : ∀ X4 : G, (M.op x y) = (M.op (M.op x y) X4) := by
    intro X4
    first
    | (have i₁ := eq2962802 X4 x x
       have i₂ := eq2962103 x x
       grind)
    | exact superpose eq2962103 eq2962802
    | exact resolve eq2962802 eq2962103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2962103 eq2962802
  have eq2964210 : ∀ X0 X1 : G, (M.op x y) = (M.op (τ X0) (τ X0)) ∨ (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2961280 (τ X0) (τ X1)
       have i₂ := eq5841 X1 X0
       grind)
    | exact superpose eq5841 eq2961280
    | (have j1 := eq5841 X1 X0
       grind)
    | exact resolve eq2961280 eq5841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5841 eq2961280
  have eq2964300 : ∀ X0 X1 : G, (M.op x y) = (τ (M.op X0 X0)) ∨ (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2964210 X0 X1
       have i₂ := eq2527855 X0
       grind)
    | exact superpose eq2527855 eq2964210
    | (have j0 := eq2964210 X0 X1
       grind)
    | exact resolve eq2964210 eq2527855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2527855 eq2964210
  have eq2971243 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2962077 (M.op x y)
       have i₂ := eq2963499 (M.op x y)
       grind)
    | exact superpose eq2963499 eq2962077
    | exact resolve eq2962077 eq2963499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2962077 eq2963499
  have eq2971695 : (M.op x y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq2971243
       have i₂ := eq2524882 (M.op x y)
       grind)
    | exact superpose eq2524882 eq2971243
    | exact resolve eq2971243 eq2524882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2971243
  have eq2971868 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq2971695
       have i₂ := eq2960470 (M.op x y)
       grind)
    | exact superpose eq2960470 eq2971695
    | exact resolve eq2971695 eq2960470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2971695
  have eq2971885 : (M.op x y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2971868
       grind)
    | exact superpose eq2971868 eq16
    | exact resolve eq16 eq2971868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2971889 : (M.op x y) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq25735
       have i₂ := eq2971868
       grind)
    | exact superpose eq2971868 eq25735
    | exact resolve eq25735 eq2971868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25735
  have eq3002239 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2524927 X1 X0
       have i₂ := eq2754084 X0 X1
       grind)
    | exact superpose eq2754084 eq2524927
    | (have j0 := eq2524927 X0 X1
       have j1 := eq2754084 X1 X0
       grind)
    | exact resolve eq2524927 eq2754084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2524927 eq2754084
  have eq3002568 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq3002239 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq3002239 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq3002239 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq3002239 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3002239
  have eq3022357 : ∀ X0 X1 : G, (M.op (τ X1) X0) = (τ (k X1 (σ X0))) ∨ (M.op x y) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2964300 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2964300
    | (have j0 := eq2964300 (σ X0) X1
       grind)
    | exact resolve eq2964300 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2964300
  have eq3022451 : ∀ X0 X1 : G, (M.op (τ X1) X0) = (k (τ X1) X0) ∨ (M.op x y) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3022357 X0 X1
       have i₂ := eq30 X1 X0
       grind)
    | exact superpose eq30 eq3022357
    | (have j0 := eq3022357 X0 X1
       grind)
    | exact resolve eq3022357 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3022357
  have eq3022473 : ∀ X0 X1 : G, (M.op x y) = (τ (σ (M.op X0 X0))) ∨ (M.op (τ X1) X0) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3022451 X0 X1
       have i₂ := eq2524882 X0
       grind)
    | exact superpose eq2524882 eq3022451
    | (have j0 := eq3022451 X0 X1
       grind)
    | exact resolve eq3022451 eq2524882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2524882 eq3022451
  have eq3022483 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op x y) ∨ (M.op (τ X1) X0) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3022473 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq3022473
    | (have j0 := eq3022473 X0 X1
       grind)
    | exact resolve eq3022473 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3022473
  have eq3022495 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op x y) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3022483 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3022483
    | (have j0 := eq3022483 X1 X1
       grind)
    | exact resolve eq3022483 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3022483
  have eq3022984 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2971868
       have i₂ := eq3022495 X0 X1
       grind)
    | exact superpose eq3022495 eq2971868
    | (have j1 := eq3022495 X1 X0
       grind)
    | exact resolve eq2971868 eq3022495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3023586 : ∀ X0 : G, (M.op x y) ≠ (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq2971889
       have i₂ := eq3022984 x X0
       grind)
    | exact superpose eq3022984 eq2971889
    | (have j1 := eq3022984 x X0
       grind)
    | exact resolve eq2971889 eq3022984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2971889 eq3022984
  have eq3023664 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ x)) ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq3023586 X0
       have j1 := eq3022495 X0 x
       grind)
    | (have r₁ := eq3023586 X0
       have r₂ := eq3022495 X0 x
       grind)
    | exact resolve eq3023586 eq3022495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3022495 eq3023586
  have eq3023901 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (σ y)) ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq2958873 (σ x) (σ y)
       have i₂ := eq3023664 X0
       grind)
    | exact superpose eq3023664 eq2958873
    | (have j1 := eq3023664 X0
       grind)
    | exact resolve eq2958873 eq3023664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3023664
  have eq3023951 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq3023901 X0
       grind)
    | (have r₁ := eq3023901 X0
       have r₂ := eq2971885
       grind)
    | exact resolve eq3023901 eq2971885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3023901
  have eq3024065 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 x) ∨ (M.op (σ X0) (σ x)) = (σ (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq3002568 X0 x
       have i₂ := eq3023951 X0
       grind)
    | exact superpose eq3023951 eq3002568
    | (have j0 := eq3002568 X0 x
       grind)
    | exact resolve eq3002568 eq3023951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3002568 eq3023951
  have eq3035624 : (M.op x y) = (M.op y x) ∨ (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq2944907
       have i₂ := eq3024065 y
       grind)
    | exact superpose eq3024065 eq2944907
    | (have j1 := eq3024065 y
       grind)
    | exact resolve eq2944907 eq3024065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2944907 eq3024065
  have eq3035629 : y = (M.op x y) ∨ (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq3035624
       have i₂ := eq2934404
       grind)
    | exact superpose eq2934404 eq3035624
    | exact resolve eq3035624 eq2934404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3035624
  have eq3035635 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3035629
       have i₂ := eq2934404
       grind)
    | exact superpose eq2934404 eq3035629
    | exact resolve eq3035629 eq2934404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2934404 eq3035629
  have eq3035669 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2958873 (σ x) (σ y)
       have i₂ := eq3035635
       grind)
    | exact superpose eq3035635 eq2958873
    | exact resolve eq2958873 eq3035635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2958873 eq3035635
  have eq3035673 : y = (M.op x y) := by
    first
    | (have r₁ := eq3035669
       have r₂ := eq2971885
       grind)
    | exact resolve eq3035669 eq2971885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3035669
  have eq3035861 : ∀ X3 : G, y = (M.op X3 y) := by
    intro X3
    first
    | (have i₁ := eq2960470 X3
       have i₂ := eq3035673
       grind)
    | exact superpose eq3035673 eq2960470
    | exact resolve eq2960470 eq3035673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2960470
  have eq3036158 : y = (σ y) := by
    first
    | (have i₁ := eq2971868
       have i₂ := eq3035673
       grind)
    | exact superpose eq3035673 eq2971868
    | exact resolve eq2971868 eq3035673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2971868
  have eq3036159 : y ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2971885
       have i₂ := eq3035673
       grind)
    | exact superpose eq3035673 eq2971885
    | exact resolve eq2971885 eq3035673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2971885 eq3035673
  have eq3043085 : y ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq3036159
       have i₂ := eq3036158
       grind)
    | exact superpose eq3036158 eq3036159
    | exact resolve eq3036159 eq3036158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3036158 eq3036159
  have eq3043779 : False := by grind
  exact eq3043779

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pyx_pyx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq556 X0
       grind)
    | exact superpose eq556 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X1 : G, (k X1 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq558 X0 X1
       have i₂ := eq556 X1
       grind)
    | exact superpose eq556 eq558
    | (have j0 := eq558 X0 X1
       grind)
    | (have r₁ := eq558 X0 X0
       have r₂ := eq556 X0
       grind)
    | exact resolve eq558 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq1094 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ x = y ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq9
    | (have j1 := eq11 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq11 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1095 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq1094
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq1094
    | exact resolve eq1094 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094
  have eq1104 : (M.op x x) = (k y y) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1095
       have i₂ := eq556 y
       grind)
    | exact superpose eq556 eq1095
    | exact resolve eq1095 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095
  have eq1113 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k y y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1104
       have i₂ := eq556 x
       grind)
    | exact superpose eq556 eq1104
    | exact resolve eq1104 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1199 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k y y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1113
       have i₂ := eq11 (σ x) (σ y)
       grind)
    | exact superpose eq11 eq1113
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq1113
       have r₂ := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq1113
       have r₂ := eq11 (M.op (σ x) (σ y)) (k (σ x) (σ y))
       grind)
    | (have r₁ := eq1113
       have r₂ := eq11 (k (σ x) (σ y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1113 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113
  have eq1200 : (k y y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
  clear eq1199
  have eq1201 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k y y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1200
       have i₂ := eq556 (σ y)
       grind)
    | exact superpose eq556 eq1200
    | exact resolve eq1200 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq1202 : x = y ∨ (k y y) = (k x x) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1201
       have i₂ := eq556 (σ x)
       grind)
    | exact superpose eq556 eq1201
    | exact resolve eq1201 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq1274 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (k y y) = (k x x) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1202
       grind)
    | exact superpose eq1202 eq9
    | exact resolve eq9 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202
  have eq1275 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (k y y) = (k x x) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1274
       have i₂ := eq556 x
       grind)
    | exact superpose eq556 eq1274
    | exact resolve eq1274 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1274
  have eq1276 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (k y y) = (k x x) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1275
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1275
    | exact resolve eq1275 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275
  have eq1277 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (k y y) = (k x x) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1276
       have i₂ := eq556 (σ x)
       grind)
    | exact superpose eq556 eq1276
    | (have r₁ := eq1276
       have r₂ := eq556 (σ x)
       grind)
    | exact resolve eq1276 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276
  have eq1278 : (k y y) = (k x x) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1277
  have eq1355 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq1278
       grind)
    | exact superpose eq1278 eq10
    | exact resolve eq10 eq1278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278
  have eq1357 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1355
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1355
    | exact resolve eq1355 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355
  have eq1358 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1357
  have eq1361 : (k y y) = (τ (k (σ x) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18 y y
       have i₂ := eq1358
       grind)
    | exact superpose eq1358 eq18
    | exact resolve eq18 eq1358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1407 : (k y y) = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1361
       have i₂ := eq18 x x
       grind)
    | exact superpose eq18 eq1361
    | exact resolve eq1361 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1361
  have eq19291 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ y) X0) ∨ (k X0 X0) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq565 (σ y) X0
       have i₂ := eq1358
       grind)
    | exact superpose eq1358 eq565
    | (have j0 := eq565 (σ x) X0
       grind)
    | (have r₁ := eq565 (σ x) (σ y)
       have r₂ := eq1358
       grind)
    | (have r₁ := eq565 (σ y) (σ x)
       have r₂ := eq1358
       grind)
    | exact resolve eq565 eq1358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358
  have eq19357 : ∀ X0 : G, (k X0 X0) ≠ (k x x) ∨ (M.op X0 y) = (k y X0) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq565 y X0
       have i₂ := eq1407
       grind)
    | exact superpose eq1407 eq565
    | (have j0 := eq565 x X0
       grind)
    | (have r₁ := eq565 x y
       have r₂ := eq1407
       grind)
    | (have r₁ := eq565 y x
       have r₂ := eq1407
       grind)
    | exact resolve eq565 eq1407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565 eq1407
  have eq20427 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have j0 := eq19357 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19357
  have eq20453 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq20427
       grind)
    | exact superpose eq20427 eq9
    | exact resolve eq9 eq20427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20427
  have eq20534 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20453
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq20453
    | exact resolve eq20453 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20453
  have eq22043 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20534
       have i₂ := eq19291 (σ x)
       grind)
    | exact superpose eq19291 eq20534
    | (have j1 := eq19291 (σ x)
       grind)
    | (have r₁ := eq20534
       have r₂ := eq19291 (σ x)
       grind)
    | exact resolve eq20534 eq19291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19291 eq20534
  have eq22056 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by grind
  clear eq22043
  have eq22057 : (σ x) = (σ y) := by grind
  clear eq22056
  have eq22135 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq22057
       grind)
    | exact superpose eq22057 eq15
    | exact resolve eq15 eq22057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22057
  have eq22270 : x = y := by
    first
    | (have i₁ := eq22135
       have i₂ := eq15 x
       grind)
    | exact superpose eq15 eq22135
    | exact resolve eq22135 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22135
  have eq22276 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq22270
       grind)
    | exact superpose eq22270 eq9
    | exact resolve eq9 eq22270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22270
  have eq22277 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by
    first
    | (have i₁ := eq22276
       have i₂ := eq556 x
       grind)
    | exact superpose eq556 eq22276
    | exact resolve eq22276 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22276
  have eq22278 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq22277
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq22277
    | exact resolve eq22277 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22277
  have eq22279 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq22278
       have i₂ := eq556 (σ x)
       grind)
    | exact superpose eq556 eq22278
    | (have r₁ := eq22278
       have r₂ := eq556 (σ x)
       grind)
    | exact resolve eq22278 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556 eq22278
  have eq22280 : False := by grind
  exact eq22280

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_y_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq19 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq28 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
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
       have i₂ := eq28 (σ X0)
       grind)
    | exact superpose eq28 eq15
    | exact resolve eq15 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq28 (τ X0)
       grind)
    | exact superpose eq28 eq17
    | exact resolve eq17 eq28
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
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq31
    | exact resolve eq31 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq28 X0
       grind)
    | exact superpose eq28 eq33
    | exact resolve eq33 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq33
  have eq45 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq51 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 X1
       have i₂ := eq34 X1
       grind)
    | exact superpose eq34 eq71
    | (have j0 := eq71 X0 X1
       grind)
    | exact resolve eq71 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq82 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq95 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq10
    | exact resolve eq10 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq106 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq19 X1 X0 X3
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq150 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq75
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq176 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq150 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq150
    | (have j0 := eq150 X0 X1
       grind)
    | exact resolve eq150 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq180 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq176 X0 X1
       have j1 := eq82 X1 X0
       grind)
    | (have r₁ := eq176 X1 X0
       have r₂ := eq82 X0 X1
       grind)
    | exact resolve eq176 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq176
  have eq491 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq180 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq180
    | exact resolve eq180 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq504 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq180 (σ X0) X1
       grind)
    | exact superpose eq180 eq15
    | (have j1 := eq180 (σ X0) X1
       grind)
    | exact resolve eq15 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq525 : ∀ X0 X1 : G, (τ X1) = (M.op X0 (τ X1)) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq491 (τ X1) X0
       grind)
    | exact superpose eq491 eq18
    | (have j1 := eq491 (τ X1) X0
       grind)
    | exact resolve eq18 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq534 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq491 X1 (τ X0)
       grind)
    | exact superpose eq491 eq17
    | (have j1 := eq491 X1 (τ X0)
       grind)
    | exact resolve eq17 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq786 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq106 x X2 X0 X1
       grind)
    | exact superpose eq106 eq9
    | exact resolve eq9 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq819 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq786 x X1 X0
       grind)
    | exact superpose eq786 eq9
    | exact resolve eq9 eq786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq1194 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq534 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq534
    | exact resolve eq534 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq1264 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1194 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1194
    | (have j0 := eq1194 X0 X1
       grind)
    | exact resolve eq1194 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194
  have eq1754 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ X0) (τ X0)) ∨ (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (τ X1)
       have i₂ := eq525 X0 X1
       grind)
    | exact superpose eq525 eq12
    | (have j1 := eq525 X1 X0
       grind)
    | exact resolve eq12 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1760 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq819 (τ X1) X0
       have i₂ := eq525 X0 X1
       grind)
    | exact superpose eq525 eq819
    | (have j1 := eq525 (τ X0) X0
       grind)
    | exact resolve eq819 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525 eq819
  have eq1778 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1760 X0 X1
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq1760
    | (have j0 := eq1760 X0 X1
       grind)
    | exact resolve eq1760 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1760
  have eq1784 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1754 X0 X1
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq1754
    | (have j0 := eq1754 X0 X1
       grind)
    | exact resolve eq1754 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq1754
  have eq1817 : ∀ X0 X1 : G, (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1784 X0 X1
       have j1 := eq1778 X0 X1
       grind)
    | (have r₁ := eq1784 X0 X1
       have r₂ := eq1778 X0 X1
       grind)
    | exact resolve eq1784 eq1778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1778 eq1784
  have eq3623 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X0))) = (k (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq1817 X0 (τ X1)
       grind)
    | exact superpose eq1817 eq17
    | (have j1 := eq1817 X0 (τ X1)
       grind)
    | exact resolve eq17 eq1817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1817
  have eq3632 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ (M.op (τ X1) (τ X0))) = (k (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3623 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3623
    | (have j0 := eq3623 X0 X1
       grind)
    | exact resolve eq3623 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3623
  have eq3647 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3632 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3632
    | (have j0 := eq3632 X0 X1
       grind)
    | exact resolve eq3632 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3632
  have eq3780 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op (τ (σ X0)) (τ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3647 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3647
    | exact resolve eq3647 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3791 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq491 X0 X1
       have i₂ := eq3647 X0 X1
       grind)
    | exact superpose eq3647 eq491
    | (have j0 := eq491 X0 X1
       have j1 := eq3647 X0 X1
       grind)
    | exact resolve eq491 eq3647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491 eq3647
  have eq3831 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3791 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3791
  have eq3867 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op (τ (σ X0)) X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3780 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3780
    | (have j0 := eq3780 X0 X1
       grind)
    | exact resolve eq3780 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3780
  have eq3887 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3867 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3867
    | (have j0 := eq3867 X0 X1
       grind)
    | exact resolve eq3867 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3867
  have eq3948 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X1))
       have i₂ := eq3831 X1 X0
       grind)
    | exact superpose eq3831 eq10
    | (have j1 := eq3831 X1 X0
       grind)
    | exact resolve eq10 eq3831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3831
  have eq4106 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq504 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq4192 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4106 (τ X0) (τ X1)
       have i₂ := eq51 X1 X0
       grind)
    | exact superpose eq51 eq4106
    | (have j0 := eq4106 (τ X0) (τ X1)
       grind)
    | exact resolve eq4106 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq4204 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4192 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq4192
    | (have j0 := eq4192 X0 X1
       grind)
    | exact resolve eq4192 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4192
  have eq4210 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4204 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4204
    | (have j0 := eq4204 X0 X1
       grind)
    | exact resolve eq4204 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4204
  have eq4212 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4210 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4210
    | (have j0 := eq4210 X0 X1
       grind)
    | exact resolve eq4210 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4210
  have eq4213 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4212 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4212
    | (have j0 := eq4212 X0 X1
       grind)
    | exact resolve eq4212 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4212
  have eq4812 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3948 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3948
    | (have j0 := eq3948 (σ X0) X1
       grind)
    | exact resolve eq3948 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3948
  have eq4952 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4812 X0 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq4812
    | (have j0 := eq4812 X0 X1
       grind)
    | exact resolve eq4812 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4812
  have eq5308 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (M.op X0 (τ X1))) ∨ (σ (τ X1)) = (M.op (σ X0) (σ (τ X1))) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4106 X0 (τ X1)
       have i₂ := eq4952 X0 X1
       grind)
    | exact superpose eq4952 eq4106
    | (have j0 := eq4106 X0 (τ X1)
       have j1 := eq4952 X0 (σ (τ X1))
       grind)
    | exact resolve eq4106 eq4952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4106 eq4952
  have eq5328 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ X0) (σ (τ X1))) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5308 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5308
    | (have j0 := eq5308 X0 X1
       grind)
    | exact resolve eq5308 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5308
  have eq5335 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (σ (M.op X0 (τ X1))) ≠ X1 ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5328 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5328
    | (have j0 := eq5328 X0 X1
       grind)
    | exact resolve eq5328 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5328
  have eq5336 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) ≠ X1 ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5335 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5335
  have eq5346 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5336 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5336
    | (have j0 := eq5336 X1 (σ X0)
       grind)
    | exact resolve eq5336 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5336
  have eq6463 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq3887 X0 X1
       grind)
    | exact superpose eq3887 eq10
    | (have j1 := eq3887 X0 X1
       grind)
    | exact resolve eq10 eq3887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3887
  have eq6528 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6463 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq6463
    | (have j0 := eq6463 X0 X1
       grind)
    | exact resolve eq6463 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6463
  have eq6955 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq6528 X1 X0
       grind)
    | exact superpose eq6528 eq10
    | (have j1 := eq6528 X1 X0
       grind)
    | exact resolve eq10 eq6528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6528
  have eq7020 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6955 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6955
    | (have j0 := eq6955 X0 X1
       grind)
    | exact resolve eq6955 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6955
  have eq7073 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq7020 X1 (σ X0)
       grind)
    | exact superpose eq7020 eq45
    | (have j1 := eq7020 X1 (σ X0)
       grind)
    | exact resolve eq45 eq7020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq7020
  have eq10057 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X1) X0
       have i₂ := eq7073 X1 (σ X0)
       grind)
    | exact superpose eq7073 eq26
    | (have j1 := eq7073 X1 (σ X0)
       grind)
    | exact resolve eq26 eq7073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq7073
  have eq10114 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10057 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq10057
    | (have j0 := eq10057 X0 X1
       grind)
    | exact resolve eq10057 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10057
  have eq10145 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10114 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10114
    | (have j0 := eq10114 X0 X1
       grind)
    | exact resolve eq10114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10114
  have eq10154 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10145 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10145
    | (have j0 := eq10145 X0 X1
       grind)
    | exact resolve eq10145 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10145
  have eq10467 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4213 X1 X0
       have i₂ := eq10154 X0 X1
       grind)
    | exact superpose eq10154 eq4213
    | (have j0 := eq4213 X1 X0
       have j1 := eq10154 X0 X1
       grind)
    | (have r₁ := eq4213 X1 X0
       have r₂ := eq10154 X0 X1
       grind)
    | exact resolve eq4213 eq10154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4213 eq10154
  have eq10545 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq10467 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10467
  have eq10754 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq10545 X1 X0
       grind)
    | exact superpose eq10545 eq11
    | (have j1 := eq10545 X1 X0
       grind)
    | exact resolve eq11 eq10545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10545
  have eq11426 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10754 x y
       grind)
    | exact superpose eq10754 eq16
    | (have j1 := eq10754 x y
       grind)
    | exact resolve eq16 eq10754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10754
  have eq11530 : y = (M.op x y) := by
    first
    | (have j1 := eq1264 x y
       grind)
    | (have r₁ := eq11426
       have r₂ := eq1264 x y
       grind)
    | exact resolve eq11426 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264 eq11426
  have eq11658 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5346 y x
       have i₂ := eq11530
       grind)
    | exact superpose eq11530 eq5346
    | (have j0 := eq5346 y x
       grind)
    | exact resolve eq5346 eq11530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5346
  have eq11667 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11658
  have eq12053 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11667
       grind)
    | exact superpose eq11667 eq16
    | exact resolve eq16 eq11667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11667
  have eq12092 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq12053
       have i₂ := eq11530
       grind)
    | exact superpose eq11530 eq12053
    | exact resolve eq12053 eq11530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11530 eq12053
  have eq12093 : False := by grind
  exact eq12093

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_y_pyy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq23 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
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
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq72 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 (τ X1)) ∨ (M.op (τ X1) (τ X1)) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) X0
       have i₂ := eq33 (σ X0)
       grind)
    | exact superpose eq33 eq22
    | exact resolve eq22 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq81 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq33 (τ X0)
       grind)
    | exact superpose eq33 eq18
    | exact resolve eq18 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq82 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81
    | exact resolve eq81 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq83 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq80 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq80
    | exact resolve eq80 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq90 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq82
    | exact resolve eq82 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq83
    | exact resolve eq83 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq83
  have eq94 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq90 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq10
    | exact resolve eq10 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq23 X1 X0 X3
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq137 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (σ X0) (σ X1)
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq42
    | (have j0 := eq42 (σ X0) (σ X1)
       have j1 := eq66 X0 X1
       grind)
    | (have r₁ := eq42 (σ X0) (σ X1)
       have r₂ := eq66 X0 X1
       grind)
    | exact resolve eq42 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq142 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq137 X0 X1
       have j1 := eq42 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq137 X0 X1
       have r₂ := eq42 (σ X0) (σ X1)
       grind)
    | exact resolve eq137 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq146 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq142 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq142 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq142 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | exact resolve eq142 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq148 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq146 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq146
    | (have j0 := eq146 X0 X1
       grind)
    | exact resolve eq146 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq179 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op X1 (τ X0)) ∨ (k X1 (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (τ X0)
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq12
    | exact resolve eq12 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480 : ∀ X0 X1 : G, (τ X1) = (M.op X0 (τ X1)) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1
       have i₂ := eq101 X1
       grind)
    | exact superpose eq101 eq72
    | (have j0 := eq72 X0 X1
       grind)
    | exact resolve eq72 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq527 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (τ (M.op X0 X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X1 (τ X0)
       have i₂ := eq480 X1 X0
       grind)
    | exact superpose eq480 eq42
    | (have j0 := eq42 X1 (τ X0)
       have j1 := eq480 X1 X0
       grind)
    | (have r₁ := eq42 X0 (τ X1)
       have r₂ := eq480 X0 X1
       grind)
    | exact resolve eq42 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq533 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X1 X1)) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq480 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (τ (M.op X0 X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq527 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq537 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (τ (M.op X0 X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq534 X0 X1
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq534
    | (have j0 := eq534 X0 X1
       grind)
    | exact resolve eq534 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq670 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 X1
       have i₂ := eq94 X1
       grind)
    | exact superpose eq94 eq148
    | (have j0 := eq148 X0 X1
       grind)
    | exact resolve eq148 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq682 : ∀ X0 X1 : G, (σ X1) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq670 (τ X0) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq670
    | exact resolve eq670 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq670
  have eq973 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq112 x X2 X0 X1
       grind)
    | exact superpose eq112 eq9
    | exact resolve eq9 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq1089 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq140 X0 X1
       have i₂ := eq94 X1
       grind)
    | exact superpose eq94 eq140
    | (have j0 := eq140 X0 X1
       grind)
    | exact resolve eq140 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq1090 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1089 X0 X1
       have i₂ := eq94 X1
       grind)
    | exact superpose eq94 eq1089
    | (have j0 := eq1089 X0 X1
       grind)
    | exact resolve eq1089 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089
  have eq1095 : ∀ X0 X1 : G, (σ (σ (k X0 X1))) ≠ (σ (M.op (σ X1) (σ X1))) ∨ (σ (M.op (σ X1) (σ X1))) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1090 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1090
    | (have j0 := eq1090 (σ X0) (σ X1)
       grind)
    | exact resolve eq1090 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1125 : ∀ X0 X1 : G, (σ (σ (k X0 X1))) ≠ (σ (σ (M.op X1 X1))) ∨ (σ (M.op (σ X1) (σ X1))) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1095 X0 X1
       have i₂ := eq94 X1
       grind)
    | exact superpose eq94 eq1095
    | (have j0 := eq1095 X0 X1
       grind)
    | exact resolve eq1095 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095
  have eq1137 : ∀ X0 X1 : G, (σ (σ (k X0 X1))) ≠ (σ (σ (M.op X1 X1))) ∨ (σ (σ (M.op X1 X1))) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1125 X0 X1
       have i₂ := eq94 X1
       grind)
    | exact superpose eq94 eq1125
    | (have j0 := eq1125 X0 X1
       grind)
    | exact resolve eq1125 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq3266 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq973 X0 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq973 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq973 eq973
    | exact resolve eq973 eq973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq3316 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (τ (M.op X0 X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3266 (τ X1) X0
       have i₂ := eq480 X0 X1
       grind)
    | exact superpose eq480 eq3266
    | (have j1 := eq480 X1 X0
       grind)
    | exact resolve eq3266 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480 eq3266
  have eq3391 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (τ (M.op X0 X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3316 X0 X1
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq3316
    | (have j0 := eq3316 X0 X1
       grind)
    | exact resolve eq3316 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq3316
  have eq3393 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (τ (M.op X0 X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3391 X0 X1
       have j1 := eq533 X1 X0
       grind)
    | (have r₁ := eq3391 X1 X1
       have r₂ := eq533 X0 X1
       grind)
    | exact resolve eq3391 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533 eq3391
  have eq3492 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (k X1 (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq537 X0 X1
       have j1 := eq179 X0 X1
       grind)
    | (have r₁ := eq537 X0 X1
       have r₂ := eq179 X0 X1
       grind)
    | exact resolve eq537 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq537
  have eq3493 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3492 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3492
    | exact resolve eq3492 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3492
  have eq3589 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3493 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3493
    | (have j0 := eq3493 X0 X1
       grind)
    | exact resolve eq3493 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3493
  have eq3605 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3589 X0 X1
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq3589
    | (have j0 := eq3589 X0 X1
       grind)
    | exact resolve eq3589 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3589
  have eq3701 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq3605 X1 X0
       grind)
    | exact superpose eq3605 eq10
    | (have j1 := eq3605 X1 X0
       grind)
    | exact resolve eq10 eq3605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3757 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3701 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq3701
    | (have j0 := eq3701 X0 X1
       grind)
    | exact resolve eq3701 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3701
  have eq3865 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3757 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3757
    | exact resolve eq3757 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3757
  have eq3963 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3865 X0 X1
       have i₂ := eq94 X1
       grind)
    | exact superpose eq94 eq3865
    | (have j0 := eq3865 X0 X1
       grind)
    | exact resolve eq3865 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3865
  have eq5770 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3393 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3393
    | exact resolve eq3393 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3393
  have eq5867 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5770 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5770
    | (have j0 := eq5770 X0 X1
       grind)
    | exact resolve eq5770 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5770
  have eq5873 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5867 X0 X1
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq5867
    | (have j0 := eq5867 X0 X1
       grind)
    | exact resolve eq5867 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq5867
  have eq5920 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq5873 X1 X0
       grind)
    | exact superpose eq5873 eq10
    | (have j1 := eq5873 X1 X0
       grind)
    | exact resolve eq10 eq5873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5873
  have eq5986 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5920 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq5920
    | (have j0 := eq5920 X0 X1
       grind)
    | exact resolve eq5920 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5920
  have eq6035 : ∀ X0 X1 : G, (σ X1) ≠ (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq682 X0 X1
       have i₂ := eq5986 X0 (σ X1)
       grind)
    | exact superpose eq5986 eq682
    | (have j1 := eq5986 X0 (σ X1)
       grind)
    | exact resolve eq682 eq5986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq6065 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq5986 (σ X0) (σ X1)
       grind)
    | exact superpose eq5986 eq15
    | (have j1 := eq5986 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq5986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5986
  have eq6104 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6065 X0 X1
       have i₂ := eq94 X1
       grind)
    | exact superpose eq94 eq6065
    | (have j0 := eq6065 X0 X1
       grind)
    | exact resolve eq6065 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6065
  have eq6120 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) ≠ (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6035 X0 X1
       have i₂ := eq94 X1
       grind)
    | exact superpose eq94 eq6035
    | (have j0 := eq6035 X0 X1
       grind)
    | exact resolve eq6035 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq6035
  have eq6121 : ∀ X0 X1 : G, (σ X1) ≠ (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq6120 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6120
  have eq10282 : ∀ X0 X1 : G, (σ (σ (τ (k X0 X1)))) ≠ (σ (σ (M.op (τ X1) (τ X1)))) ∨ (σ (σ (M.op (τ X1) (τ X1)))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1137 (τ X0) (τ X1)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq1137
    | (have j0 := eq1137 (τ X0) (τ X1)
       grind)
    | exact resolve eq1137 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137
  have eq10358 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (M.op (τ X1) (τ X1)))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq10282 X0 X1
       have i₂ := eq90 X1
       grind)
    | exact superpose eq90 eq10282
    | (have j0 := eq10282 X0 X1
       grind)
    | exact resolve eq10282 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10282
  have eq10401 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (σ (M.op (τ X1) (τ X1)))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq10358 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq10358
    | (have j0 := eq10358 X0 X1
       grind)
    | exact resolve eq10358 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10358
  have eq10433 : ∀ X0 X1 : G, (σ (σ (M.op (τ X1) (τ X1)))) = (M.op (σ (σ (τ X0))) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq10401 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq10401
    | (have j0 := eq10401 X0 X1
       grind)
    | exact resolve eq10401 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10401
  have eq10461 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (σ (M.op (τ X1) (τ X1)))) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq10433 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10433
    | (have j0 := eq10433 X0 X1
       grind)
    | exact resolve eq10433 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10433
  have eq10485 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq10461 X0 X1
       have i₂ := eq90 X1
       grind)
    | exact superpose eq90 eq10461
    | (have j0 := eq10461 X0 X1
       grind)
    | exact resolve eq10461 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10461
  have eq10502 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (σ (τ X0))) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10485 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10485
    | (have j0 := eq10485 X0 X1
       grind)
    | exact resolve eq10485 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10485
  have eq10514 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10502 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10502
    | (have j0 := eq10502 X0 X1
       grind)
    | exact resolve eq10502 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10502
  have eq10522 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq10514 X0 X1
       have j1 := eq6121 (σ X0) X1
       grind)
    | (have r₁ := eq10514 X0 X1
       have r₂ := eq6121 (σ X0) X1
       grind)
    | exact resolve eq10514 eq6121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6121 eq10514
  have eq10538 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10522 (τ X0) (τ X1)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq10522
    | (have j0 := eq10522 (τ X0) (τ X1)
       grind)
    | exact resolve eq10522 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq10613 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10538 X0 X1
       have i₂ := eq90 X1
       grind)
    | exact superpose eq90 eq10538
    | (have j0 := eq10538 X0 X1
       grind)
    | exact resolve eq10538 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10538
  have eq10648 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10613 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq10613
    | (have j0 := eq10613 X0 X1
       grind)
    | exact resolve eq10613 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10613
  have eq10676 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10648 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq10648
    | (have j0 := eq10648 X0 X1
       grind)
    | exact resolve eq10648 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10648
  have eq10695 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10676 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10676
    | (have j0 := eq10676 X0 X1
       grind)
    | exact resolve eq10676 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10676
  have eq10703 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10695 X0 X1
       have i₂ := eq90 X1
       grind)
    | exact superpose eq90 eq10695
    | (have j0 := eq10695 X0 X1
       grind)
    | exact resolve eq10695 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq10695
  have eq12549 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3963 x y
       grind)
    | exact superpose eq3963 eq16
    | (have j1 := eq3963 x y
       grind)
    | exact resolve eq16 eq3963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3963
  have eq12961 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq12549
       have i₂ := eq3605 y x
       grind)
    | exact superpose eq3605 eq12549
    | (have j1 := eq3605 y x
       grind)
    | (have r₁ := eq12549
       have r₂ := eq3605 y x
       grind)
    | exact resolve eq12549 eq3605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12549
  have eq12964 : (k x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq12961
  have eq34982 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6104 x y
       grind)
    | exact superpose eq6104 eq16
    | (have j1 := eq6104 x y
       grind)
    | exact resolve eq16 eq6104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6104
  have eq35191 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq34982
       have i₂ := eq3605 y x
       grind)
    | exact superpose eq3605 eq34982
    | (have j1 := eq3605 y x
       grind)
    | (have r₁ := eq34982
       have r₂ := eq3605 y x
       grind)
    | exact resolve eq34982 eq3605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3605 eq34982
  have eq35194 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (k x y) = (M.op y y) := by grind
  clear eq35191
  have eq35703 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35194
       grind)
    | exact superpose eq35194 eq16
    | exact resolve eq16 eq35194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35194
  have eq35741 : (k x y) = (M.op y y) := by
    first
    | (have r₁ := eq35703
       have r₂ := eq12964
       grind)
    | exact resolve eq35703 eq12964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12964 eq35703
  have eq35786 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10522 x y
       have i₂ := eq35741
       grind)
    | exact superpose eq35741 eq10522
    | (have j0 := eq10522 x y
       grind)
    | exact resolve eq10522 eq35741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10522
  have eq35787 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10703 x y
       have i₂ := eq35741
       grind)
    | exact superpose eq35741 eq10703
    | (have j0 := eq10703 x y
       grind)
    | (have r₁ := eq10703 x y
       have r₂ := eq35741
       grind)
    | exact resolve eq10703 eq35741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10703 eq35741
  have eq35798 : (M.op x y) = (M.op y y) := by grind
  clear eq35787
  have eq35799 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq35786
  have eq38012 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35799
       have i₂ := eq35798
       grind)
    | exact superpose eq35798 eq35799
    | exact resolve eq35799 eq35798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35798 eq35799
  have eq38013 : False := by grind
  exact eq38013

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(Y,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyy_x_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq20 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq9 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
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
  have eq32 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
  have eq33 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq29 (τ X0)
       grind)
    | exact superpose eq29 eq18
    | exact resolve eq18 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33
    | exact resolve eq33 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq29 X0
       grind)
    | exact superpose eq29 eq32
    | exact resolve eq32 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq37 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq29 X0
       grind)
    | exact superpose eq29 eq34
    | exact resolve eq34 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq34
  have eq39 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq41 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X1
       have i₂ := eq35 X1
       grind)
    | exact superpose eq35 eq39
    | (have j0 := eq39 X0 X1
       grind)
    | exact resolve eq39 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq35 X1
       grind)
    | exact superpose eq35 eq41
    | (have j0 := eq41 X0 X1
       grind)
    | exact resolve eq41 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq91 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq21 (σ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq21
    | exact resolve eq21 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq35
  have eq118 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq20 X1 X0 X3
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq163 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq43
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq188 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq163 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq163
    | (have j0 := eq163 X0 X1
       grind)
    | exact resolve eq163 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq194 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq188 X0 X1
       have j1 := eq91 X1 X0
       grind)
    | (have r₁ := eq188 (M.op X1 (σ X0)) X0
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq188 X1 X0
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq188 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq188
  have eq452 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq194 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq194
    | (have j0 := eq194 X1 (τ X0)
       grind)
    | exact resolve eq194 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq194 (σ X0) X1
       grind)
    | exact superpose eq194 eq15
    | (have j1 := eq194 (σ X0) X1
       grind)
    | exact resolve eq15 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq477 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq452 X0 X1
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq452
    | (have j0 := eq452 X0 X1
       grind)
    | exact resolve eq452 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq452
  have eq495 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq477 X1 (τ X0)
       grind)
    | exact superpose eq477 eq18
    | (have j1 := eq477 X1 (τ X0)
       grind)
    | exact resolve eq18 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq477
  have eq693 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq118 x X2 X0 X1
       grind)
    | exact superpose eq118 eq9
    | exact resolve eq9 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq726 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq693 x X1 X0
       grind)
    | exact superpose eq693 eq9
    | exact resolve eq9 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq756 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 X0) X0
       have i₂ := eq726 X0 X1
       grind)
    | exact superpose eq726 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq726 X1 X1
       grind)
    | exact resolve eq12 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1446 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq495 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq495
    | exact resolve eq495 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq1521 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1446 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1446
    | (have j0 := eq1446 X0 X1
       grind)
    | exact resolve eq1446 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446
  have eq2110 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq464 x y
       grind)
    | exact superpose eq464 eq16
    | (have j1 := eq464 x y
       grind)
    | exact resolve eq16 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq2206 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2110
       have i₂ := eq1521 x y
       grind)
    | exact superpose eq1521 eq2110
    | (have j1 := eq1521 x y
       grind)
    | (have r₁ := eq2110
       have r₂ := eq1521 x y
       grind)
    | exact resolve eq2110 eq1521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521
  have eq2207 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq2206
  have eq2333 : x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq726 y y
       have i₂ := eq2207
       grind)
    | exact superpose eq2207 eq726
    | exact resolve eq726 eq2207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2334 : x ≠ x ∨ x = (k x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq756 y y
       have i₂ := eq2207
       grind)
    | exact superpose eq2207 eq756
    | exact resolve eq756 eq2207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756 eq2207
  have eq2335 : x = (k x y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq2334
  have eq2443 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2110
       have i₂ := eq2335
       grind)
    | exact superpose eq2335 eq2110
    | exact resolve eq2110 eq2335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2110 eq2335
  have eq2454 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq2443
  have eq2455 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2454
       have i₂ := eq2333
       grind)
    | exact superpose eq2333 eq2454
    | exact resolve eq2454 eq2333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2333 eq2454
  have eq2456 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq2455
  have eq2457 : (σ x) = (σ (M.op y y)) := by grind
  clear eq2456
  have eq2540 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq92 y
       have i₂ := eq2457
       grind)
    | exact superpose eq2457 eq92
    | exact resolve eq92 eq2457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq2541 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2457
       grind)
    | exact superpose eq2457 eq10
    | exact resolve eq10 eq2457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2457
  have eq2589 : x = (M.op y y) := by
    first
    | (have i₁ := eq2541
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2541
    | exact resolve eq2541 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2541
  have eq2614 : x = (M.op x y) := by
    first
    | (have i₁ := eq726 y y
       have i₂ := eq2589
       grind)
    | exact superpose eq2589 eq726
    | exact resolve eq726 eq2589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726 eq2589
  have eq2777 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2540
       grind)
    | exact superpose eq2540 eq16
    | exact resolve eq16 eq2540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2540
  have eq2797 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2777
       have i₂ := eq2614
       grind)
    | exact superpose eq2614 eq2777
    | exact resolve eq2777 eq2614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2614 eq2777
  have eq2798 : False := by grind
  exact eq2798
