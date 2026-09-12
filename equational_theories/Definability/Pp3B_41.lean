import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pyy_pyx_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq87 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq87
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq87
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
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
  have eq101 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq272 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq35
  have eq283 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq272 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq272
    | exact resolve eq272 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq284 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq283
  have eq410 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (σ (M.op X0 X0))) X2) X1) = X2 := by
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
  clear eq53 eq54
  have eq598 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq284 X0
       grind)
    | exact superpose eq284 eq16
    | exact resolve eq16 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq1123 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op X1 X1))) = X3 := by
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
  have eq1685 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (σ (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq565 (M.op X0 (σ (M.op X1 X1))) X0 X2
       have i₂ := eq410 X1 X0 (M.op X0 (σ (M.op X1 X1)))
       grind)
    | exact superpose eq410 eq565
    | exact resolve eq565 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq565
  have eq8001 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1123 X1 (τ X0) X2
       have i₂ := eq598 X0
       grind)
    | exact superpose eq598 eq1123
    | exact resolve eq1123 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598 eq1123
  have eq61648 : ∀ X0 : G, y = (M.op (M.op y x) (M.op y (σ (M.op X0 X0)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1685 y X0 y
       have i₂ := eq101
       grind)
    | exact superpose eq101 eq1685
    | exact resolve eq1685 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq61652 : x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq61648 x
       have i₂ := eq1685 y x x
       grind)
    | exact superpose eq1685 eq61648
    | exact resolve eq61648 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1685 eq61648
  have eq61653 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq61652
  have eq61690 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq61653 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq61653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61653
  have eq61691 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq61690
    | exact resolve eq61690 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61690
  have eq61702 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq61691
       have r₂ := eq28
       grind)
    | exact resolve eq61691 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61691
  have eq61961 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (τ (M.op X0 X0)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq61702 eq8001
    | exact resolve eq8001 eq61702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61702
  have eq61962 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq61961 x
       have i₂ := eq8001 x sF3 sF2
       grind)
    | exact superpose eq8001 eq61961
    | exact resolve eq61961 eq8001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8001 eq61961
  have eq61963 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq61962
  have eq61993 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq61963 eq30
    | exact resolve eq30 eq61963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq61963
  have eq62120 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq61993
    | exact resolve eq61993 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq61993
  have eq62121 : x = y := by grind
  clear eq62120
  have eq62500 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq62121
       grind)
    | exact superpose eq62121 eq19
    | exact resolve eq19 eq62121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq62501 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq62121
       grind)
    | exact superpose eq62121 eq25
    | exact resolve eq25 eq62121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq62121
  have eq62629 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq62501
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq62501
    | exact resolve eq62501 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq62501
  have eq62661 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq62629 eq27
    | exact resolve eq27 eq62629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq62629
  have eq63949 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq62661 eq66
    | exact resolve eq66 eq62661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq62661
  have eq64268 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq63949
       have i₂ := eq62500
       grind)
    | exact superpose eq62500 eq63949
    | exact resolve eq63949 eq62500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62500 eq63949
  have eq64283 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq64268 eq15
    | exact resolve eq15 eq64268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64268
  have eq64364 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq64283
    | exact resolve eq64283 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq64283
  have eq64387 : False := by grind
  exact eq64387

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_x_pyx_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq87 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq87
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq87
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
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
  have eq101 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq272 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq35
  have eq283 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq272 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq272
    | exact resolve eq272 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq284 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq283
  have eq410 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (σ (M.op X0 X0))) X2) X1) = X2 := by
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
  have eq569 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq284 X0
       grind)
    | exact superpose eq284 eq16
    | exact resolve eq16 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq707 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) = X2 := by
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
  clear eq53 eq54
  have eq1122 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op X1 X1))) = X3 := by
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
  have eq1684 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (σ (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq707 (M.op X0 (σ (M.op X1 X1))) X0 X2
       have i₂ := eq410 X1 X0 (M.op X0 (σ (M.op X1 X1)))
       grind)
    | exact superpose eq410 eq707
    | exact resolve eq707 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq707
  have eq8068 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1122 X1 (τ X0) X2
       have i₂ := eq569 X0
       grind)
    | exact superpose eq569 eq1122
    | exact resolve eq1122 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569 eq1122
  have eq61643 : ∀ X0 : G, y = (M.op (M.op y x) (M.op y (σ (M.op X0 X0)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1684 y X0 y
       have i₂ := eq101
       grind)
    | exact superpose eq101 eq1684
    | exact resolve eq1684 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq61647 : x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq61643 x
       have i₂ := eq1684 y x x
       grind)
    | exact superpose eq1684 eq61643
    | exact resolve eq61643 eq1684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1684 eq61643
  have eq61648 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq61647
  have eq61685 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq61648 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq61648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61648
  have eq61686 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq61685
    | exact resolve eq61685 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61685
  have eq61697 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq61686
       have r₂ := eq28
       grind)
    | exact resolve eq61686 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61686
  have eq61956 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (τ (M.op X0 X0)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq61697 eq8068
    | exact resolve eq8068 eq61697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61697
  have eq61957 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq61956 x
       have i₂ := eq8068 x sF3 sF2
       grind)
    | exact superpose eq8068 eq61956
    | exact resolve eq61956 eq8068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8068 eq61956
  have eq61958 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq61957
  have eq61988 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq61958 eq30
    | exact resolve eq30 eq61958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq61958
  have eq62115 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq61988
    | exact resolve eq61988 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq61988
  have eq62116 : x = y := by grind
  clear eq62115
  have eq62495 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq62116
       grind)
    | exact superpose eq62116 eq19
    | exact resolve eq19 eq62116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq62496 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq62116
       grind)
    | exact superpose eq62116 eq25
    | exact resolve eq25 eq62116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq62116
  have eq62624 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq62496
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq62496
    | exact resolve eq62496 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq62496
  have eq62656 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq62624 eq27
    | exact resolve eq27 eq62624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq62624
  have eq63944 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq62656 eq66
    | exact resolve eq66 eq62656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq62656
  have eq64263 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq63944
       have i₂ := eq62495
       grind)
    | exact superpose eq62495 eq63944
    | exact resolve eq63944 eq62495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62495 eq63944
  have eq64278 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq64263 eq15
    | exact resolve eq15 eq64263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64263
  have eq64359 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq64278
    | exact resolve eq64278 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq64278
  have eq64382 : False := by grind
  exact eq64382

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_x_pyx_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
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
  have eq30 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq40 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq30
    | (have j0 := eq30 X0 X1
       grind)
    | exact resolve eq30 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq74 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (σ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X1 X2 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq25
    | exact resolve eq25 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq75 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
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
  have eq82 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X2 X2)) (M.op X1 X1) X1
       have i₂ := eq25 (M.op X1 X1) X0 X2
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq25 X1 (M.op X0 X0) X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X1 (M.op X2 X2)) X0))) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 (M.op (M.op X1 (M.op X2 X2)) X0) X3 X4 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X1) = (M.op X0 (M.op (M.op (M.op X4 X4) (M.op X5 X5)) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq24 (M.op X1 X0) X4 X5 (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X1)
       have i₂ := eq24 X1 X2 X3 X0
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 x (M.op X0 X0) X2
       have i₂ := eq25 x (M.op X0 X0) X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq203 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq40
    | (have j0 := eq40 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | exact resolve eq40 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq776 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op (M.op X3 X3) (M.op X4 X4)) X2)) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X2 X3 X4 X2
       have i₂ := eq75 X1 X0 X2
       grind)
    | (have i₁ := eq24 (M.op X1 X1) X1 X2 (M.op X0 X0)
       have i₂ := eq75 X0 X1 X2
       grind)
    | exact superpose eq75 eq24
    | exact resolve eq24 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq1168 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X2) X3) (M.op (M.op X0 X0) (M.op X1 X1))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq84 X2 (M.op X0 X0) X3
       have i₂ := eq82 (M.op X0 X0) X0 X1
       grind)
    | (have i₁ := eq84 X2 (M.op X0 X0) X3
       have i₂ := eq82 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq82 eq84
    | exact resolve eq84 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq1280 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X3) X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq109 X0 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X3
       have i₂ := eq24 X0 X1 X2 X0
       grind)
    | exact superpose eq24 eq109
    | exact resolve eq109 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1594 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X1 (σ (M.op X0 X0)) (M.op X1 X1)
       have i₂ := eq74 X0 (M.op X1 X1) (σ (M.op X0 X0))
       grind)
    | exact superpose eq74 eq84
    | exact resolve eq84 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq84
  have eq6478 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 : G, (M.op (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op X2 (M.op X5 (M.op X6 X6)))) (M.op (M.op (M.op X7 X7) (M.op X8 X8)) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2))) = X5 := by
    intro X0 X1 X2 X3 X4 X5 X6 X7 X8
    first
    | (have i₁ := eq95 (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op X2 (M.op X5 (M.op X6 X6)))) X5 X6 X7 X8
       have i₂ := eq99 (M.op X5 (M.op X6 X6)) X2 X0 X1 X3 X4
       grind)
    | exact superpose eq99 eq95
    | exact resolve eq95 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq99
  have eq6496 : ∀ X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op X2 (M.op X5 (M.op X6 X6)))) X2) = X5 := by
    intro X2 X3 X4 X5 X6
    first
    | (have i₁ := eq6478 x x X2 X3 X4 X5 X6 x x
       have i₂ := eq776 x x X2 x x
       grind)
    | exact superpose eq776 eq6478
    | exact resolve eq6478 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776 eq6478
  have eq14973 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) (M.op (M.op X2 X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq109 X2 X1 X1
       have i₂ := eq1594 X0 X1
       grind)
    | exact superpose eq1594 eq109
    | exact resolve eq109 eq1594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23879 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (M.op X2 X2) (σ X1))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq109 X2 (σ X1) (σ X0)
       have i₂ := eq203 X1 X0
       grind)
    | exact superpose eq203 eq109
    | (have j1 := eq203 X1 X0
       grind)
    | exact resolve eq109 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq203
  have eq24157 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23879 X0 X1 x
       have i₂ := eq14973 X0 (σ X1) x
       grind)
    | exact superpose eq14973 eq23879
    | (have j0 := eq23879 X0 X1 x
       grind)
    | exact resolve eq23879 eq14973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14973 eq23879
  have eq24158 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq24157 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24157
  have eq344444 : ∀ X0 X3 X4 : G, (M.op X0 (M.op X3 (M.op X0 (M.op X4 X4)))) = X3 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq1280 (M.op X3 (M.op X0 (M.op X4 X4))) x x X3
       have i₂ := eq6496 X3 x x X0 X4
       grind)
    | exact superpose eq6496 eq1280
    | exact resolve eq1280 eq6496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280 eq6496
  have eq351350 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq344444 (M.op (M.op X1 X1) X0) X2 (M.op x x)
       have i₂ := eq1168 x x X1 X0
       grind)
    | exact superpose eq1168 eq344444
    | exact resolve eq344444 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168 eq344444
  have eq671331 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq24158 y x
       grind)
    | exact superpose eq24158 eq16
    | (have j1 := eq24158 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq24158 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq24158 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq24158 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq24158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24158
  have eq674366 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq671331
  have eq737224 : ∀ X0 : G, y = (M.op (M.op (M.op X0 X0) y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq351350 y X0 y
       have i₂ := eq674366
       grind)
    | exact superpose eq674366 eq351350
    | exact resolve eq351350 eq674366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674366
  have eq737228 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq737224 x
       have i₂ := eq351350 y x x
       grind)
    | exact superpose eq351350 eq737224
    | exact resolve eq737224 eq351350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351350 eq737224
  have eq737229 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq737228
  have eq838548 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq737229
       grind)
    | exact superpose eq737229 eq10
    | exact resolve eq10 eq737229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737229
  have eq838715 : x = y ∨ x = y := by
    first
    | (have i₁ := eq838548
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq838548
    | exact resolve eq838548 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838548
  have eq838716 : x = y := by grind
  clear eq838715
  have eq908817 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq838716
       grind)
    | exact superpose eq838716 eq16
    | exact resolve eq16 eq838716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838716
  have eq908818 : False := by grind
  exact eq908818

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_x_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = a :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq54 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
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
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq54
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
  have eq1147 : ∀ X0 X2 : G, (M.op X2 X2) = (M.op X0 X0) := by
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
  have eq1194 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 x X0
       have r₂ := eq1147 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq1147 X0 x
       grind)
    | exact resolve eq13 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1282 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1194 (σ X1) (σ X0)
       grind)
    | exact superpose eq1194 eq15
    | (have j1 := eq1194 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1290 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1282 X0 X1
       have i₂ := eq1194 X1 X0
       grind)
    | exact superpose eq1194 eq1282
    | (have j0 := eq1282 X0 X1
       have j1 := eq1194 (σ (M.op X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq1282 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194 eq1282
  have eq1864 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1
       have i₂ := eq1147 X0 (τ X1)
       grind)
    | (have i₁ := eq55 X1
       have i₂ := eq1147 (τ X1) X0
       grind)
    | exact superpose eq1147 eq55
    | exact resolve eq55 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1147
  have eq3696 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1290 x y
       grind)
    | exact superpose eq1290 eq16
    | (have j1 := eq1290 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1290 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1290 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq1290 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq1290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq3705 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq3696
  have eq5762 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3705
       grind)
    | exact superpose eq3705 eq10
    | exact resolve eq10 eq3705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3705
  have eq5785 : x = y ∨ x = y := by
    first
    | (have i₁ := eq5762
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5762
    | exact resolve eq5762 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5762
  have eq5786 : x = y := by grind
  clear eq5785
  have eq9040 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5786
       grind)
    | exact superpose eq5786 eq16
    | exact resolve eq16 eq5786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5786
  have eq9041 : False := by grind
  exact eq9041

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_pxy_pyx_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq46 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq45
  have eq49 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  clear eq37
  have eq52 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq49
  have eq53 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq52
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
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
  have eq55 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
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
  have eq67 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq53
       grind)
    | exact superpose eq53 eq16
    | exact resolve eq16 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq83 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq84 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq38
  have eq88 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq84
  have eq89 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq88
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq83
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq83
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq83 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq90
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq90
    | exact resolve eq90 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq22 eq96
    | exact resolve eq96 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq122 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq268 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq270 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq36
  have eq280 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq268 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq268
    | exact resolve eq268 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq281 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq280
  have eq406 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq408 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k X0 (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq406 X0
       have i₂ := eq10 X0 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq406
    | (have j0 := eq406 X0
       grind)
    | exact resolve eq406 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq478 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (σ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X1 X2 (σ X0)
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq55
    | exact resolve eq55 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq55 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       have i₂ := eq14 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq28 eq54
    | (have j0 := eq54 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq54 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 x (M.op X0 X0) X2
       have i₂ := eq55 x (M.op X0 X0) X0
       grind)
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq595 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq281 X0
       grind)
    | exact superpose eq281 eq16
    | exact resolve eq16 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq815 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq479 (M.op X1 X1) x X0
       have i₂ := eq55 x (M.op X1 X1) X1
       grind)
    | exact superpose eq55 eq479
    | exact resolve eq479 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq479
  have eq863 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq815 (σ X0) X1
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq815
    | exact resolve eq815 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq1355 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 X0) x)) := by
    intro X0
    first
    | (have i₁ := eq562 X0 x y
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq562
    | (have j0 := eq562 X0 x y
       grind)
    | exact resolve eq562 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq2180 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op X0 X0)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq555 x (σ (M.op X0 X0))
       have i₂ := eq478 X0 x (σ (M.op X0 X0))
       grind)
    | exact superpose eq478 eq555
    | exact resolve eq555 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478 eq555
  have eq10410 : ∀ X0 : G, (k X0 (σ (τ (M.op X0 X0)))) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq270 X0
       have i₂ := eq595 X0
       grind)
    | exact superpose eq595 eq270
    | (have j0 := eq270 X0
       grind)
    | exact resolve eq270 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq10411 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10410 X0
       have i₂ := eq15 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq10410
    | (have j0 := eq10410 X0
       grind)
    | exact resolve eq10410 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10410
  have eq10412 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10411 X0
       have i₂ := eq595 X0
       grind)
    | exact superpose eq595 eq10411
    | (have j0 := eq10411 X0
       grind)
    | exact resolve eq10411 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595 eq10411
  have eq10779 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (σ (M.op (τ (σ X0)) (τ (σ (M.op X0 X0))))) ∨ (τ (σ X0)) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10412 (σ X0)
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq10412
    | exact resolve eq10412 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq10412
  have eq10837 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (σ (M.op (τ (σ X0)) (M.op X0 X0))) ∨ (τ (σ X0)) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10779 X0
       have i₂ := eq16 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq10779
    | (have j0 := eq10779 X0
       grind)
    | exact resolve eq10779 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10779
  have eq10857 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) ∨ (τ (σ X0)) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10837 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq10837
    | (have j0 := eq10837 X0
       grind)
    | exact resolve eq10837 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10837
  have eq10872 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) ∨ (τ (σ X0)) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10857 X0
       have i₂ := eq10 X0 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq10857
    | (have j0 := eq10857 X0
       grind)
    | exact resolve eq10857 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10857
  have eq10875 : ∀ X0 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10872 X0
       have i₂ := eq16 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq10872
    | (have j0 := eq10872 X0
       grind)
    | exact resolve eq10872 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10872
  have eq10878 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10875 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq10875
    | (have j0 := eq10875 X0
       grind)
    | exact resolve eq10875 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10875
  have eq25700 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq25701 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq28 eq25700
    | exact resolve eq25700 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25700
  have eq25706 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq25701
       have r₂ := eq29
       grind)
    | exact resolve eq25701 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25701
  have eq25710 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq25706 eq122
    | exact resolve eq122 eq25706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq25706
  have eq25880 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq30 eq25710
    | exact resolve eq25710 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25710
  have eq25881 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq25880
  have eq25902 : (σ (k y x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq408 y
       have i₂ := eq25881
       grind)
    | exact superpose eq25881 eq408
    | exact resolve eq408 eq25881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq25956 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq863 y X0
       have i₂ := eq25881
       grind)
    | exact superpose eq25881 eq863
    | exact resolve eq863 eq25881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq25981 : y = (M.op (M.op x y) (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1355 y
       have i₂ := eq25881
       grind)
    | exact superpose eq25881 eq1355
    | exact resolve eq1355 eq25881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355
  have eq26006 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2180 y
       have i₂ := eq25881
       grind)
    | exact superpose eq25881 eq2180
    | exact resolve eq2180 eq25881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2180
  have eq26043 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq26006
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26006
    | exact resolve eq26006 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26006
  have eq26067 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq25956 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25956
    | (have j0 := eq25956 X0
       grind)
    | exact resolve eq25956 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25956
  have eq26075 : (σ (k y x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25902
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25902
    | exact resolve eq25902 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25902
  have eq26085 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq26075
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq26075
    | exact resolve eq26075 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26075
  have eq26088 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq26085
       have i₂ := eq83
       grind)
    | exact superpose eq83 eq26085
    | exact resolve eq26085 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26085
  have eq26089 : (σ x) = (σ y) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq26088
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq26088
    | exact resolve eq26088 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26088
  have eq26090 : (σ x) = (σ y) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq26089
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26089
    | exact resolve eq26089 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26089
  have eq26091 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq26090
  have eq124239 : ∀ X0 : G, (M.op x y) = (M.op y (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq25981 eq481
    | exact resolve eq481 eq25981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25981
  have eq125426 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq26043 eq481
    | exact resolve eq481 eq26043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481 eq26043
  have eq168683 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq124239 y
       have i₂ := eq25881
       grind)
    | exact superpose eq25881 eq124239
    | exact resolve eq124239 eq25881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124239
  have eq168753 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq168683
  have eq176495 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq125426 x
       have i₂ := eq26067 x
       grind)
    | exact superpose eq26067 eq125426
    | exact resolve eq125426 eq26067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26067 eq125426
  have eq176695 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq176495
  have eq230882 : (σ (M.op y x)) = (σ (k y x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10878 y
       have i₂ := eq25881
       grind)
    | exact superpose eq25881 eq10878
    | exact resolve eq10878 eq25881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10878 eq25881
  have eq230982 : (σ (M.op y x)) = (σ (k y x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq230882
  have eq231036 : (σ (M.op y x)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq230982
       have i₂ := eq83
       grind)
    | exact superpose eq83 eq230982
    | exact resolve eq230982 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq230982
  have eq2054478 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq231036
       have i₂ := eq168753
       grind)
    | exact superpose eq168753 eq231036
    | exact resolve eq231036 eq168753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168753 eq231036
  have eq2054902 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2054478
  have eq2054910 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22 eq2054902
    | exact resolve eq2054902 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2054902
  have eq2054941 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2054910 eq26091
    | exact resolve eq26091 eq2054910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26091 eq2054910
  have eq2054968 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2054941
  have eq2054996 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2054968 eq176695
    | exact resolve eq176695 eq2054968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176695 eq2054968
  have eq2055074 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2054996
  have eq2055085 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2055074
       have r₂ := eq29
       grind)
    | exact resolve eq2055074 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2055074
  have eq2055089 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2055085 eq31
    | exact resolve eq31 eq2055085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2055085
  have eq2055522 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq2055089
    | exact resolve eq2055089 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2055089
  have eq2055523 : x = y := by grind
  clear eq2055522
  have eq2055557 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq2055523
       grind)
    | exact superpose eq2055523 eq20
    | exact resolve eq20 eq2055523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2055558 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq2055523
       grind)
    | exact superpose eq2055523 eq26
    | exact resolve eq26 eq2055523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2055523
  have eq2055925 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2055558
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2055558
    | exact resolve eq2055558 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2055558
  have eq2055969 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2055925 eq28
    | exact resolve eq28 eq2055925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2055925
  have eq2058661 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2055969 eq67
    | exact resolve eq67 eq2055969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq2055969
  have eq2060291 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2058661
       have i₂ := eq2055557
       grind)
    | exact superpose eq2055557 eq2058661
    | exact resolve eq2058661 eq2055557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2055557 eq2058661
  have eq2060590 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2060291 eq15
    | exact resolve eq15 eq2060291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2060291
  have eq2061362 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22 eq2060590
    | exact resolve eq2060590 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2060590
  have eq2061536 : False := by grind
  exact eq2061536

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1625 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
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
  have eq1626 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3634 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1625
       grind)
    | exact superpose eq1625 eq39
    | exact resolve eq39 eq1625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625
  have eq3635 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq3634
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3634
    | exact resolve eq3634 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3634
  have eq3637 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq20 eq3635
    | exact resolve eq3635 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3635
  have eq8072 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq3637 eq1626
    | exact resolve eq1626 eq3637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8079 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq8072
       have r₂ := eq27
       grind)
    | exact resolve eq8072 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8072
  have eq8085 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq8079 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq8079
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq8079
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq8079
       grind)
    | exact resolve eq12 eq8079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8079
  have eq8093 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq8085
  have eq8097 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq8093
       have r₂ := eq26
       grind)
    | exact resolve eq8093 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8093
  have eq8100 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq3637 eq8097
    | exact resolve eq8097 eq3637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3637 eq8097
  have eq8102 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq8100
       have r₂ := eq27
       grind)
    | exact resolve eq8100 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8100
  have eq8105 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq8102
       grind)
    | exact superpose eq8102 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq8102
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq8102
       grind)
    | exact resolve eq12 eq8102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8102
  have eq8113 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq8105
  have eq8117 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8113
       have r₂ := eq18
       grind)
    | exact resolve eq8113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8113
  have eq8121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq8117
       grind)
    | exact superpose eq8117 eq39
    | exact resolve eq39 eq8117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8117
  have eq8122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8121
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8121
    | exact resolve eq8121 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8121
  have eq8124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq8122
    | exact resolve eq8122 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8122
  have eq8133 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq8124 eq1626
    | exact resolve eq1626 eq8124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1626
  have eq8137 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8133
  have eq8142 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq8137
       have r₂ := eq27
       grind)
    | exact resolve eq8137 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8137
  have eq8156 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8142 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq8142
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq8142
       grind)
    | exact resolve eq12 eq8142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8142
  have eq8164 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq8156
  have eq8168 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq8164
       have r₂ := eq26
       grind)
    | exact resolve eq8164 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8164
  have eq8171 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq8124 eq8168
    | exact resolve eq8168 eq8124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8124 eq8168
  have eq8173 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq8171
       have r₂ := eq27
       grind)
    | exact resolve eq8171 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8171
  have eq8176 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq8173 eq31
    | exact resolve eq31 eq8173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq8173
  have eq8196 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq8176
    | exact resolve eq8176 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq8176
  have eq8197 : x = y := by grind
  clear eq8196
  have eq8199 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq8197
       grind)
    | exact superpose eq8197 eq18
    | exact resolve eq18 eq8197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq8200 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq8197
       grind)
    | exact superpose eq8197 eq24
    | exact resolve eq24 eq8197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq8197
  have eq8213 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq8200
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8200
    | exact resolve eq8200 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8200
  have eq8214 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq8199
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq8199
    | exact resolve eq8199 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8199
  have eq8215 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq8213 eq26
    | exact resolve eq26 eq8213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq8213
  have eq8236 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq8215
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq8215
    | exact resolve eq8215 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq8215
  have eq8240 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq8214
       grind)
    | exact superpose eq8214 eq39
    | exact resolve eq39 eq8214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq8214
  have eq8426 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq8240
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8240
    | exact resolve eq8240 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq8240
  have eq8480 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8236 eq8426
    | exact resolve eq8426 eq8236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8236 eq8426
  have eq8502 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq8480
    | exact resolve eq8480 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq8480
  have eq8508 : False := by grind
  exact eq8508

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxy_pxx_pyx_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq16 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (k X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X0 X1 X2
       have i₂ := eq174 X2
       grind)
    | exact superpose eq174 eq176
    | exact resolve eq176 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq179 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) (M.op X1 (k X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq177
    | exact resolve eq177 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq181 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (k X0 X0)) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X2) (k X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (k X1 X1) (k X0 X0)
       have i₂ := eq179 X1 (k X0 X0) X0
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq568 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op (k X1 X1) X0)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq181 x (M.op (k X1 X1) X0) X3
       have i₂ := eq543 X1 x X0
       grind)
    | exact superpose eq543 eq181
    | exact resolve eq181 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq543
  have eq1579 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op (k X1 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq568 X0 X1 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq568
    | exact resolve eq568 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1588 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (k X0 X0) x)) := by
    intro X0
    first
    | (have i₁ := eq568 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq568
    | (have j0 := eq568 x X0 y
       grind)
    | exact resolve eq568 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1589 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (k X0 X0) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq568
    | (have j0 := eq568 (σ x) X0 (σ y)
       grind)
    | exact resolve eq568 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq1625 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq1626 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1664 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1626
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq1626
    | exact resolve eq1626 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1626
  have eq1665 : (M.op x y) = (k y x) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1625
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq1625
    | exact resolve eq1625 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625
  have eq3784 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1665
       grind)
    | exact superpose eq1665 eq39
    | exact resolve eq39 eq1665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1665
  have eq3785 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq3784
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3784
    | exact resolve eq3784 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3784
  have eq3787 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq20 eq3785
    | exact resolve eq3785 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3785
  have eq14237 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq3787 eq1664
    | exact resolve eq1664 eq3787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1664 eq3787
  have eq14247 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq14237
       have r₂ := eq27
       grind)
    | exact resolve eq14237 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14237
  have eq14516 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (k X0 X0) (σ x))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq14247 eq1579
    | exact resolve eq1579 eq14247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14247
  have eq14615 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq1589 eq14516
    | exact resolve eq14516 eq1589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1589 eq14516
  have eq14616 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq14615
  have eq14764 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (k X0 X0) x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1579 x X0
       have i₂ := eq14616
       grind)
    | exact superpose eq14616 eq1579
    | exact resolve eq1579 eq14616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1579 eq14616
  have eq14890 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1588 eq14764
    | exact resolve eq14764 eq1588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1588 eq14764
  have eq14891 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq14890
  have eq14990 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq14891 eq31
    | exact resolve eq31 eq14891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq14891
  have eq15020 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq14990
    | exact resolve eq14990 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq14990
  have eq15021 : x = y := by grind
  clear eq15020
  have eq15023 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq15021
       grind)
    | exact superpose eq15021 eq18
    | exact resolve eq18 eq15021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq15024 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq15021
       grind)
    | exact superpose eq15021 eq24
    | exact resolve eq24 eq15021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq15021
  have eq15041 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq15024
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15024
    | exact resolve eq15024 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15024
  have eq15042 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq15023
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq15023
    | exact resolve eq15023 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15023
  have eq15043 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq15041 eq26
    | exact resolve eq26 eq15041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq15041
  have eq15074 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq15043
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq15043
    | exact resolve eq15043 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq15043
  have eq15079 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq15042
       grind)
    | exact superpose eq15042 eq39
    | exact resolve eq39 eq15042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq15042
  have eq15379 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq15079
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15079
    | exact resolve eq15079 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq15079
  have eq15468 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15074 eq15379
    | exact resolve eq15379 eq15074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15074 eq15379
  have eq15512 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq15468
    | exact resolve eq15468 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq15468
  have eq15531 : False := by grind
  exact eq15531

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_x_y_pyx_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq28
    | exact resolve eq28 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq28
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : x = (τ (σ x)) := by
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
  clear eq23
  have eq32 : y = (τ (σ y)) := by
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
  clear eq25
  have eq34 : (M.op x y) = (M.op x (τ (σ y))) := by
    first
    | (have i₁ := eq19
       have i₂ := eq32
       grind)
    | exact superpose eq32 eq19
    | exact resolve eq19 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq32
  have eq36 : (M.op x y) = (M.op (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq34
       have i₂ := eq31
       grind)
    | exact superpose eq31 eq34
    | exact resolve eq34 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq34
  have eq39 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
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
  have eq41 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (M.op X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X2 (M.op X0 X0)) X1
       have i₂ := eq9 (M.op X1 X1) X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq39 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq72 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq88 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq36 eq14
    | (have j0 := eq14 (M.op x y) (k (τ (σ y)) (τ (σ x)))
       grind)
    | exact resolve eq14 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 (M.op X0 X0)) X1) (M.op (M.op X2 (M.op X0 X0)) X1)) = X1 ∨ (k X2 (M.op (M.op X2 (M.op X0 X0)) X1)) = X1 ∨ (M.op (M.op X2 (M.op X0 X0)) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op (M.op X1 (M.op X2 X2)) X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq14
    | (have j0 := eq14 (M.op (M.op (M.op X2 (M.op X0 X0)) X1) (M.op (M.op X2 (M.op X0 X0)) X1)) X1
       grind)
    | exact resolve eq14 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 : G, (M.op (k X0 (M.op X1 (M.op X2 X2))) X1) = X0 ∨ (M.op (M.op X1 (M.op X2 X2)) X0) = (M.op (M.op X1 (M.op X2 X2)) (M.op X1 (M.op X2 X2))) ∨ (M.op X1 (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X2))
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 (M.op X1 (M.op X2 X2))
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 X2) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41 (M.op X0 X0) X2 (M.op X1 X1)
       have i₂ := eq41 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq41 eq41
    | exact resolve eq41 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X2) (M.op X0 X0)) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq41 X2 X3 (M.op (M.op (M.op X2 X2) (M.op X0 X0)) X1)
       have i₂ := eq9 X1 (M.op X2 X2) X0
       grind)
    | exact superpose eq9 eq41
    | exact resolve eq41 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq41 X1 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0
       grind)
    | exact superpose eq41 eq9
    | exact resolve eq9 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq41 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq41 eq9
    | exact resolve eq9 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 : G, (τ (σ y)) = (M.op (M.op x y) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (τ (σ x)))) := by
    intro X0 X1
    first
    | exact superpose eq36 eq40
    | exact resolve eq40 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op (M.op X4 X4) (M.op X3 X3)) (M.op (M.op X2 (M.op X0 X0)) X1))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq40 (M.op (M.op X2 (M.op X0 X0)) X1) X4 X3 X2
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq40
    | exact resolve eq40 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 X3) (M.op X2 X2)) X0) = (M.op X1 (M.op (M.op (M.op X5 X5) (M.op X4 X4)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq40 (M.op X0 X1) X5 X4 (M.op (M.op (M.op X3 X3) (M.op X2 X2)) X0)
       have i₂ := eq40 X0 X3 X2 X1
       grind)
    | exact superpose eq40 eq40
    | exact resolve eq40 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X3) (M.op (M.op X0 X0) X2)) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq40 X2 x (M.op X0 X0) X3
       have i₂ := eq41 X0 x (M.op X0 X0)
       grind)
    | exact superpose eq41 eq40
    | exact resolve eq40 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X1 X2 : G, (M.op X2 X2) = (M.op X1 X1) := by
    intro X1 X2
    first
    | (have i₁ := eq41 X1 x (M.op X1 X1)
       have i₂ := eq112 (M.op X1 X1) X2 x
       grind)
    | (have i₁ := eq41 x (M.op x x) (M.op x x)
       have i₂ := eq112 x (M.op (M.op x x) (M.op x x)) X2
       grind)
    | exact superpose eq112 eq41
    | exact resolve eq41 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq283 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op (M.op (M.op X3 X3) (M.op X2 X2)) X1)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq40 X1 X3 X2 X1
       have i₂ := eq213 X0 X1
       grind)
    | (have i₁ := eq40 X1 X3 X2 X1
       have i₂ := eq213 X1 X0
       grind)
    | exact superpose eq213 eq40
    | exact resolve eq40 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X2 X2)) X1 X2
       have i₂ := eq213 X0 (M.op X1 (M.op X2 X2))
       grind)
    | (have i₁ := eq9 (M.op X1 (M.op X2 X2)) X1 X2
       have i₂ := eq213 (M.op X1 (M.op X2 X2)) X0
       grind)
    | exact superpose eq213 eq9
    | exact resolve eq9 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq88 eq15
    | exact resolve eq15 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq298 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq297
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq297
    | exact resolve eq297 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq301 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | (have i₁ := eq298
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq298
    | exact resolve eq298 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq302 : (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq21 eq301
    | exact resolve eq301 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq389 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X1)) X2) = (M.op X2 (M.op (M.op (M.op X4 X4) (M.op X3 X3)) (M.op (M.op X0 (M.op X1 X1)) X2))) ∨ (k X0 (M.op (M.op X0 (M.op X1 X1)) X2)) = X2 ∨ (M.op (M.op X0 (M.op X1 X1)) X2) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq40 (M.op (M.op X0 (M.op X1 X1)) X2) X4 X3 (M.op (M.op X0 (M.op X1 X1)) X2)
       have i₂ := eq89 X1 X2 X0
       grind)
    | exact superpose eq89 eq40
    | (have j1 := eq89 X1 X2 X0
       grind)
    | exact resolve eq40 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq390 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) X2) = X0 ∨ (k X0 (M.op (M.op X0 (M.op X1 X1)) X2)) = X2 ∨ (M.op (M.op X0 (M.op X1 X1)) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq389 X0 X1 X2 x x
       have i₂ := eq132 X1 X2 X0 x x
       grind)
    | exact superpose eq132 eq389
    | (have j0 := eq389 X0 X1 X2 x x
       grind)
    | exact resolve eq389 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq391 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X0 (M.op X1 X1)) X2)) = X2 ∨ (M.op (M.op X0 (M.op X1 X1)) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq390 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq585 : ∀ X1 X2 X3 : G, (M.op (M.op X1 X3) (M.op X1 (M.op X2 X2))) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X1 (M.op X2 X2)) x
       have i₂ := eq118 X1 X2 x
       grind)
    | exact superpose eq118 eq9
    | exact resolve eq9 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq593 : ∀ X0 X1 X2 : G, (M.op (k X0 (M.op X1 (M.op X2 X2))) X1) = X0 ∨ (M.op X2 X2) = (M.op (M.op X1 (M.op X2 X2)) X0) ∨ (M.op X1 (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq92 X0 X1 X2
       have i₂ := eq585 X1 X2 (M.op X2 X2)
       grind)
    | exact superpose eq585 eq92
    | (have j0 := eq92 X0 X1 X2
       grind)
    | exact resolve eq92 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq657 : ∀ X0 X1 X3 : G, (M.op (M.op X1 X1) X0) = (M.op (M.op X3 X3) X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq41 x X1 (M.op (M.op X3 X3) X0)
       have i₂ := eq119 X3 x X0
       grind)
    | exact superpose eq119 eq41
    | exact resolve eq41 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq678 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) X0) = (M.op X2 (M.op (M.op X3 X3) (M.op X0 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq140 X3 (M.op X0 X2) (M.op (M.op X1 X1) X0)
       have i₂ := eq140 X1 X0 X2
       grind)
    | exact superpose eq140 eq140
    | exact resolve eq140 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq685 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X2) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq140 X2 X0 X0
       have i₂ := eq213 X1 X0
       grind)
    | (have i₁ := eq140 X2 X0 X0
       have i₂ := eq213 X0 X1
       grind)
    | exact superpose eq213 eq140
    | exact resolve eq140 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X0)) = (M.op X2 (M.op (M.op X3 X3) (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq140 X3 (M.op X1 X2) (M.op X1 (M.op X0 X0))
       have i₂ := eq585 X1 X0 X2
       grind)
    | exact superpose eq585 eq140
    | exact resolve eq140 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2250 : ∀ X0 X1 : G, (τ (σ x)) = (M.op (M.op x y) (M.op (M.op (M.op X1 X1) (M.op X0 X0)) (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq302 eq40
    | exact resolve eq40 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq2253 : (τ (σ x)) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq131 eq2250
    | exact resolve eq2250 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq2250
  have eq2254 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by grind
  clear eq2253
  have eq2270 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) := by
    first
    | exact superpose eq2254 eq29
    | exact resolve eq29 eq2254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2254
  have eq2382 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X0) (M.op X2 X2)) (M.op (M.op X3 (M.op X1 X1)) X4)) = (M.op X3 (M.op X4 (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq585 X4 X5 (M.op (M.op (M.op X0 X0) (M.op X2 X2)) (M.op (M.op X3 (M.op X1 X1)) X4))
       have i₂ := eq132 X1 X4 X3 X2 X0
       grind)
    | exact superpose eq132 eq585
    | exact resolve eq585 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2383 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X0) (M.op X2 X2)) (M.op (M.op X3 (M.op X1 X1)) X4)) = (M.op X3 (M.op (M.op X5 X5) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq140 X5 X4 (M.op (M.op (M.op X0 X0) (M.op X2 X2)) (M.op (M.op X3 (M.op X1 X1)) X4))
       have i₂ := eq132 X1 X4 X3 X2 X0
       grind)
    | exact superpose eq132 eq140
    | exact resolve eq140 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq2448 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2270
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq2270
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq2270
       have r₂ := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq2270
       have r₂ := eq14 (M.op (σ x) (σ y)) (k (σ y) (σ x))
       grind)
    | (have r₁ := eq2270
       have r₂ := eq14 (k (σ y) (σ x)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq2270 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2270
  have eq2449 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq2448
  have eq2491 : ∀ X1 X2 X3 : G, (k (M.op X2 X2) (M.op (M.op X1 X1) X3)) = X3 ∨ (M.op X2 X2) = (M.op (M.op X1 X1) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq391 (M.op X2 X2) x X1
       have i₂ := eq113 x X1 X2 X3
       grind)
    | (have i₁ := eq391 (M.op X1 X1) X1 X1
       have i₂ := eq113 x X1 X2 (M.op X1 X1)
       grind)
    | exact superpose eq113 eq391
    | exact resolve eq391 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq2495 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (k (M.op X2 X2) X1) ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq391 (M.op X1 X1) X1 (M.op (M.op X2 X2) X0)
       have i₂ := eq685 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq685 eq391
    | exact resolve eq391 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2498 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X2 X2)) ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq391 X1 X1 (M.op X1 (M.op X2 X2))
       have i₂ := eq585 X1 X2 (M.op X1 X1)
       grind)
    | exact superpose eq585 eq391
    | exact resolve eq391 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq585
  have eq2727 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op X4 X4) (M.op X2 X2)) (M.op X3 (M.op X5 (M.op X6 X6)))) = (M.op (M.op (M.op (M.op X1 X1) (M.op X0 X0)) X3) X5) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq9 (M.op (M.op (M.op X4 X4) (M.op X2 X2)) (M.op X3 (M.op X5 (M.op X6 X6)))) X5 X6
       have i₂ := eq134 X3 (M.op X5 (M.op X6 X6)) X0 X1 X2 X4
       grind)
    | exact superpose eq134 eq9
    | exact resolve eq9 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq2854 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (M.op X1 X1) (M.op X0 X0)) (σ x))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq2449 eq40
    | exact resolve eq40 eq2449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq2449
  have eq2860 : (σ x) = (σ y) ∨ (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2854 x x
       have i₂ := eq283 sF2 sF2 x x
       grind)
    | exact superpose eq283 eq2854
    | exact resolve eq2854 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283 eq2854
  have eq2861 : (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq2860
  have eq2871 : (σ y) = (σ (τ (σ x))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2861 eq11
    | exact resolve eq11 eq2861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2861
  have eq2872 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2871
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq2871
    | exact resolve eq2871 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2871
  have eq2873 : (σ x) = (σ y) := by grind
  clear eq2872
  have eq2875 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2873 eq29
    | exact resolve eq29 eq2873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq2877 : (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq2873 eq36
    | exact resolve eq36 eq2873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq2873
  have eq2922 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op x y)) X0) X1) = X0 := by
    intro X0 X1
    first
    | exact superpose eq2877 eq9
    | exact resolve eq9 eq2877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2927 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op x y))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq2877 eq41
    | exact resolve eq41 eq2877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq2948 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op x y) X0)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq2877 eq140
    | exact resolve eq140 eq2877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq2958 : ∀ X0 : G, (M.op x y) = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq2877 eq213
    | exact resolve eq213 eq2877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq2960 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | exact superpose eq2877 eq288
    | exact resolve eq288 eq2877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq2963 : ∀ X0 X1 : G, (M.op (k X0 (M.op X1 (M.op x y))) X1) = X0 ∨ (M.op x y) = (M.op (M.op X1 (M.op x y)) X0) ∨ (M.op X1 (M.op x y)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq2877 eq593
    | exact resolve eq593 eq2877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq2965 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op (M.op x y) X0) := by
    intro X0 X1
    first
    | exact superpose eq2877 eq657
    | exact resolve eq657 eq2877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq2966 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op (M.op x y) X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq2877 eq685
    | exact resolve eq685 eq2877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685 eq2877
  have eq2988 : ∀ X0 X2 X3 : G, (M.op X2 (M.op (M.op X3 X3) (M.op X0 X2))) = (M.op (M.op x y) X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq678 X0 x X2 X3
       have i₂ := eq2965 X0 x
       grind)
    | exact superpose eq2965 eq678
    | exact resolve eq678 eq2965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq3022 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) (M.op X2 X2)) (M.op (M.op X3 (M.op X1 X1)) X4)) = (M.op X3 (M.op (M.op x y) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2383 X0 X1 X2 X3 X4 x
       have i₂ := eq2965 X4 x
       grind)
    | exact superpose eq2965 eq2383
    | exact resolve eq2383 eq2965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2383
  have eq3026 : ∀ X1 X2 X3 : G, (k (M.op X2 X2) (M.op (M.op x y) X3)) = X3 ∨ (M.op X2 X2) = (M.op (M.op X1 X1) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq2491 X1 X2 X3
       have i₂ := eq2965 X3 X1
       grind)
    | exact superpose eq2965 eq2491
    | (have j0 := eq2491 X1 X2 X3
       grind)
    | exact resolve eq2491 eq2965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2491
  have eq3027 : ∀ X1 X2 : G, (k (M.op X2 X2) X1) = (M.op (M.op x y) X1) ∨ (M.op X2 X2) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq2495 x X1 X2
       have i₂ := eq2965 X1 x
       grind)
    | exact superpose eq2965 eq2495
    | (have j0 := eq2495 x X1 X2
       grind)
    | exact resolve eq2495 eq2965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2495
  have eq3117 : ∀ X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X5 X5))) = (M.op (M.op (M.op x y) (M.op X2 X2)) (M.op (M.op X3 (M.op X1 X1)) X4)) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2382 x X1 X2 X3 X4 X5
       have i₂ := eq2965 (M.op X2 X2) x
       grind)
    | exact superpose eq2965 eq2382
    | exact resolve eq2382 eq2965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2382
  have eq3155 : ∀ X0 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op X4 X4) (M.op X2 X2)) (M.op X3 (M.op X5 (M.op X6 X6)))) = (M.op (M.op (M.op (M.op x y) (M.op X0 X0)) X3) X5) := by
    intro X0 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq2727 X0 x X2 X3 X4 X5 X6
       have i₂ := eq2965 (M.op X0 X0) x
       grind)
    | exact superpose eq2965 eq2727
    | exact resolve eq2727 eq2965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2727
  have eq3177 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X2 (M.op (M.op x y) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq821 X0 X1 X2 x
       have i₂ := eq2965 (M.op X1 X2) x
       grind)
    | exact superpose eq2965 eq821
    | exact resolve eq821 eq2965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq3182 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2966 X0 x
       have i₂ := eq2965 (M.op sF0 X0) x
       grind)
    | exact superpose eq2965 eq2966
    | exact resolve eq2966 eq2965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2965 eq2966
  have eq3267 : ∀ X0 X1 X2 : G, (M.op x y) = X1 ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2498 X0 X1 X0
       have i₂ := eq2958 X0
       grind)
    | exact superpose eq2958 eq2498
    | (have j0 := eq2498 X0 X1 X2
       grind)
    | exact resolve eq2498 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2498
  have eq3279 : ∀ X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op x y) X1) := by
    intro X1
    first
    | (have i₁ := eq2960 x X1
       have i₂ := eq2958 x
       grind)
    | exact superpose eq2958 eq2960
    | exact resolve eq2960 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2960
  have eq3281 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2875
       have i₂ := eq2958 sF2
       grind)
    | exact superpose eq2958 eq2875
    | exact resolve eq2875 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2875
  have eq3306 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2927 X0 x
       have i₂ := eq2958 x
       grind)
    | exact superpose eq2958 eq2927
    | exact resolve eq2927 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2927
  have eq3322 : ∀ X1 X2 : G, (M.op X1 (M.op x y)) = (M.op X2 (M.op (M.op x y) (M.op X1 X2))) := by
    intro X1 X2
    first
    | (have i₁ := eq3177 x X1 X2
       have i₂ := eq2958 x
       grind)
    | exact superpose eq2958 eq3177
    | exact resolve eq3177 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3177
  have eq3344 : ∀ X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op X4 X4) (M.op X2 X2)) (M.op X3 (M.op X5 (M.op X6 X6)))) = (M.op (M.op (M.op (M.op x y) (M.op x y)) X3) X5) := by
    intro X2 X3 X4 X5 X6
    first
    | (have i₁ := eq3155 x X2 X3 X4 X5 X6
       have i₂ := eq2958 x
       grind)
    | exact superpose eq2958 eq3155
    | exact resolve eq3155 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3155
  have eq3382 : ∀ X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X5 X5))) = (M.op (M.op (M.op x y) (M.op X2 X2)) (M.op (M.op X3 (M.op x y)) X4)) := by
    intro X2 X3 X4 X5
    first
    | (have i₁ := eq3117 x X2 X3 X4 X5
       have i₂ := eq2958 x
       grind)
    | exact superpose eq2958 eq3117
    | exact resolve eq3117 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3117
  have eq3471 : ∀ X1 X2 : G, (k (M.op x y) X1) = (M.op (M.op x y) X1) ∨ (M.op X2 X2) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq3027 X1 X2
       have i₂ := eq2958 X2
       grind)
    | exact superpose eq2958 eq3027
    | (have j0 := eq3027 X1 X2
       grind)
    | exact resolve eq3027 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3027
  have eq3472 : ∀ X1 X2 X3 : G, (k (M.op x y) (M.op (M.op x y) X3)) = X3 ∨ (M.op X2 X2) = (M.op (M.op X1 X1) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq3026 X1 X2 X3
       have i₂ := eq2958 X2
       grind)
    | exact superpose eq2958 eq3026
    | (have j0 := eq3026 X1 X2 X3
       grind)
    | exact resolve eq3026 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3026
  have eq3476 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op (M.op x y) X4)) = (M.op (M.op (M.op X0 X0) (M.op X2 X2)) (M.op (M.op X3 (M.op x y)) X4)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq3022 X0 x X2 X3 X4
       have i₂ := eq2958 x
       grind)
    | exact superpose eq2958 eq3022
    | exact resolve eq3022 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3022
  have eq3508 : ∀ X0 X2 : G, (M.op (M.op x y) X0) = (M.op X2 (M.op (M.op x y) (M.op X0 X2))) := by
    intro X0 X2
    first
    | (have i₁ := eq2988 X0 X2 x
       have i₂ := eq2958 x
       grind)
    | exact superpose eq2958 eq2988
    | exact resolve eq2988 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2988
  have eq3530 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op x y)) ∨ (M.op x y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3267 X0 X1 x
       have i₂ := eq2958 x
       grind)
    | exact superpose eq2958 eq3267
    | (have j0 := eq3267 X0 X1 x
       grind)
    | exact resolve eq3267 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3267
  have eq3639 : ∀ X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op X4 X4) (M.op X2 X2)) (M.op X3 (M.op X5 (M.op X6 X6)))) = (M.op (M.op (M.op x y) X3) X5) := by
    intro X2 X3 X4 X5 X6
    first
    | (have i₁ := eq3344 X2 X3 X4 X5 X6
       have i₂ := eq2958 sF0
       grind)
    | exact superpose eq2958 eq3344
    | exact resolve eq3344 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3344
  have eq3677 : ∀ X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X5 X5))) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op X3 (M.op x y)) X4)) := by
    intro X3 X4 X5
    first
    | (have i₁ := eq3382 x X3 X4 X5
       have i₂ := eq2958 x
       grind)
    | exact superpose eq2958 eq3382
    | exact resolve eq3382 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3382
  have eq3766 : ∀ X1 : G, (k (M.op x y) X1) = (M.op (M.op x y) X1) ∨ (M.op x y) = X1 := by
    intro X1
    first
    | (have i₁ := eq3471 X1 x
       have i₂ := eq2958 x
       grind)
    | exact superpose eq2958 eq3471
    | (have j0 := eq3471 X1 x
       grind)
    | exact resolve eq3471 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3471
  have eq3767 : ∀ X2 X3 : G, (M.op X2 X2) = (M.op (M.op x y) X3) ∨ (k (M.op x y) (M.op (M.op x y) X3)) = X3 := by
    intro X2 X3
    first
    | (have i₁ := eq3472 x X2 X3
       have i₂ := eq2958 x
       grind)
    | exact superpose eq2958 eq3472
    | (have j0 := eq3472 x X2 X3
       grind)
    | exact resolve eq3472 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3472
  have eq3769 : ∀ X0 X3 X4 : G, (M.op X3 (M.op (M.op x y) X4)) = (M.op (M.op (M.op X0 X0) (M.op x y)) (M.op (M.op X3 (M.op x y)) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq3476 X0 x X3 X4
       have i₂ := eq2958 x
       grind)
    | exact superpose eq2958 eq3476
    | exact resolve eq3476 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3476
  have eq3819 : ∀ X1 : G, (M.op X1 (M.op x y)) = (k X1 (M.op x y)) ∨ (M.op x y) = X1 := by
    intro X1
    first
    | (have i₁ := eq3530 x X1
       have i₂ := eq2958 x
       grind)
    | exact superpose eq2958 eq3530
    | (have j0 := eq3530 x X1
       grind)
    | exact resolve eq3530 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3530
  have eq3899 : ∀ X2 X3 X4 X5 : G, (M.op (M.op (M.op x y) X3) X5) = (M.op (M.op (M.op X4 X4) (M.op X2 X2)) (M.op X3 (M.op X5 (M.op x y)))) := by
    intro X2 X3 X4 X5
    first
    | (have i₁ := eq3639 X2 X3 X4 X5 x
       have i₂ := eq2958 x
       grind)
    | exact superpose eq2958 eq3639
    | exact resolve eq3639 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3639
  have eq3937 : ∀ X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X5 X5))) = (M.op (M.op x y) (M.op (M.op X3 (M.op x y)) X4)) := by
    intro X3 X4 X5
    first
    | (have i₁ := eq3677 X3 X4 X5
       have i₂ := eq2958 sF0
       grind)
    | exact superpose eq2958 eq3677
    | exact resolve eq3677 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3677
  have eq4011 : ∀ X3 : G, (k (M.op x y) (M.op (M.op x y) X3)) = X3 ∨ (M.op x y) = (M.op (M.op x y) X3) := by
    intro X3
    first
    | (have i₁ := eq3767 x X3
       have i₂ := eq2958 x
       grind)
    | exact superpose eq2958 eq3767
    | (have j0 := eq3767 x X3
       grind)
    | exact resolve eq3767 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3767
  have eq4013 : ∀ X0 X3 X4 : G, (M.op X3 (M.op (M.op x y) X4)) = (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op (M.op X3 (M.op x y)) X4)) := by
    intro X0 X3 X4
    first
    | exact superpose eq3279 eq3769
    | exact resolve eq3769 eq3279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3769
  have eq4103 : ∀ X3 X4 X5 : G, (M.op (M.op (M.op x y) X3) X5) = (M.op (M.op (M.op X4 X4) (M.op x y)) (M.op X3 (M.op X5 (M.op x y)))) := by
    intro X3 X4 X5
    first
    | (have i₁ := eq3899 x X3 X4 X5
       have i₂ := eq2958 x
       grind)
    | exact superpose eq2958 eq3899
    | exact resolve eq3899 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3899
  have eq4139 : ∀ X3 X4 : G, (M.op (M.op x y) (M.op (M.op X3 (M.op x y)) X4)) = (M.op X3 (M.op X4 (M.op x y))) := by
    intro X3 X4
    first
    | (have i₁ := eq3937 X3 X4 x
       have i₂ := eq2958 x
       grind)
    | exact superpose eq2958 eq3937
    | exact resolve eq3937 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3937
  have eq4201 : ∀ X3 X4 : G, (M.op X3 (M.op (M.op x y) X4)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op X3 (M.op x y)) X4)) := by
    intro X3 X4
    first
    | (have i₁ := eq4013 x X3 X4
       have i₂ := eq2958 x
       grind)
    | exact superpose eq2958 eq4013
    | exact resolve eq4013 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4013
  have eq4263 : ∀ X3 X4 X5 : G, (M.op (M.op (M.op x y) X3) X5) = (M.op (M.op (M.op x y) (M.op X4 X4)) (M.op X3 (M.op X5 (M.op x y)))) := by
    intro X3 X4 X5
    first
    | exact superpose eq3279 eq4103
    | exact resolve eq4103 eq3279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4103
  have eq4348 : ∀ X3 X4 : G, (M.op X3 (M.op (M.op x y) X4)) = (M.op (M.op x y) (M.op (M.op X3 (M.op x y)) X4)) := by
    intro X3 X4
    first
    | (have i₁ := eq4201 X3 X4
       have i₂ := eq2958 sF0
       grind)
    | exact superpose eq2958 eq4201
    | exact resolve eq4201 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4201
  have eq4382 : ∀ X3 X5 : G, (M.op (M.op (M.op x y) (M.op x y)) (M.op X3 (M.op X5 (M.op x y)))) = (M.op (M.op (M.op x y) X3) X5) := by
    intro X3 X5
    first
    | (have i₁ := eq4263 X3 x X5
       have i₂ := eq2958 x
       grind)
    | exact superpose eq2958 eq4263
    | exact resolve eq4263 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4263
  have eq4479 : ∀ X3 X5 : G, (M.op (M.op (M.op x y) X3) X5) = (M.op (M.op x y) (M.op X3 (M.op X5 (M.op x y)))) := by
    intro X3 X5
    first
    | (have i₁ := eq4382 X3 X5
       have i₂ := eq2958 sF0
       grind)
    | exact superpose eq2958 eq4382
    | exact resolve eq4382 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4382
  have eq4881 : ∀ X0 X1 : G, (M.op (M.op (k X0 (M.op x y)) X1) X0) = X1 ∨ (M.op x y) = X0 := by
    intro X0 X1
    first
    | exact superpose eq3819 eq2922
    | (have j1 := eq3819 X0
       grind)
    | exact resolve eq2922 eq3819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2922
  have eq4883 : ∀ X0 : G, (M.op (M.op x y) (k X0 (M.op x y))) = X0 ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq3819 eq3306
    | (have j1 := eq3819 X0
       grind)
    | exact resolve eq3306 eq3819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3819
  have eq4998 : ∀ X0 : G, (k (M.op x y) X0) = (k X0 (M.op x y)) ∨ (M.op x y) = X0 ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq4883 eq4011
    | (have j1 := eq4883 X0
       grind)
    | exact resolve eq4011 eq4883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4011 eq4883
  have eq5001 : ∀ X0 : G, (k (M.op x y) X0) = (k X0 (M.op x y)) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have j0 := eq4998 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4998
  have eq5011 : ∀ X0 : G, (τ (k (M.op x y) X0)) = (k (τ X0) (τ (M.op x y))) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq5001 eq72
    | (have j1 := eq5001 X0
       grind)
    | exact resolve eq72 eq5001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5001
  have eq5016 : ∀ X0 : G, (k (τ (M.op x y)) (τ X0)) = (k (τ X0) (τ (M.op x y))) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq5011 X0
       have i₂ := eq72 X0 sF0
       grind)
    | exact superpose eq72 eq5011
    | (have j0 := eq5011 X0
       grind)
    | exact resolve eq5011 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5011
  have eq5167 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (k X0 (M.op x y))) X0) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq3279 eq4881
    | (have j0 := eq4881 (M.op (M.op (M.op x y) (k X0 (M.op x y))) X0) x
       grind)
    | exact resolve eq4881 eq3279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4881
  have eq5176 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op (k X0 (M.op x y)) (M.op X0 (M.op x y)))) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq4479 eq5167
    | (have j0 := eq5167 (M.op (M.op x y) (M.op (k X0 (M.op x y)) (M.op X0 (M.op x y))))
       grind)
    | exact resolve eq5167 eq4479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5167
  have eq5200 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 (M.op x y))) = (M.op X0 (M.op X1 (M.op (M.op x y) X0))) := by
    intro X0 X1
    first
    | exact superpose eq4348 eq3508
    | exact resolve eq3508 eq4348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5204 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) X0) = (M.op (M.op x y) (M.op X1 (M.op (M.op x y) X0))) := by
    intro X0 X1
    first
    | exact superpose eq4348 eq3182
    | exact resolve eq3182 eq4348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4348
  have eq5208 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op x y) (M.op X1 (M.op (M.op x y) X0))) ∨ (M.op (k X0 (M.op X1 (M.op x y))) X1) = X0 ∨ (M.op X1 (M.op x y)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq5204 eq2963
    | (have j0 := eq2963 X0 X1
       grind)
    | exact resolve eq2963 eq5204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2963
  have eq5220 : ∀ X3 X4 : G, (M.op X3 (M.op X4 (M.op x y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op X3 (M.op (M.op x y) X4)))) := by
    intro X3 X4
    first
    | exact superpose eq5204 eq4139
    | exact resolve eq4139 eq5204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4139 eq5204
  have eq5234 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op x y) X0))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq3306 eq5200
    | exact resolve eq5200 eq3306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5200
  have eq5244 : ∀ X3 X4 : G, (M.op X3 (M.op (M.op x y) X4)) = (M.op X3 (M.op X4 (M.op x y))) := by
    intro X3 X4
    first
    | exact superpose eq3182 eq5220
    | exact resolve eq5220 eq3182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3182 eq5220
  have eq5544 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ (M.op (k X0 (M.op X1 (M.op x y))) X1) = X0 ∨ (M.op X1 (M.op x y)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq5208 eq3322
    | (have j1 := eq5208 X0 X1
       grind)
    | exact resolve eq3322 eq5208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3322 eq5208
  have eq5555 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op x y) (M.op X0 (M.op (M.op x y) (M.op x y)))) ∨ (M.op (k X0 (M.op X1 (M.op x y))) X1) = X0 ∨ (M.op X1 (M.op x y)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq4479 eq5544
    | (have j0 := eq5544 X0 X1
       grind)
    | exact resolve eq5544 eq4479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5544
  have eq5568 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = X0 ∨ (M.op (k X0 (M.op X1 (M.op x y))) X1) = X0 ∨ (M.op X1 (M.op x y)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq5234 eq5555
    | (have j0 := eq5555 X0 X1
       grind)
    | exact resolve eq5555 eq5234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5555
  have eq5569 : ∀ X0 X1 : G, (M.op (k X0 (M.op X1 (M.op x y))) X1) = X0 ∨ (M.op X1 (M.op x y)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq5568 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5568
  have eq8237 : ∀ X0 X1 : G, (M.op (k X1 (M.op (M.op x y) X0)) X0) = X1 ∨ (M.op (M.op x y) X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq3279 eq5569
    | exact resolve eq5569 eq3279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3279 eq5569
  have eq8389 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op (k X0 (M.op x y)) (M.op (M.op x y) X0))) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq5244 eq5176
    | (have j0 := eq5176 (M.op (M.op x y) (M.op (k X0 (M.op x y)) (M.op (M.op x y) X0)))
       grind)
    | exact resolve eq5176 eq5244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5176 eq5244
  have eq8933 : ∀ X0 X1 : G, (M.op (k X1 X0) (M.op X0 (M.op x y))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | exact superpose eq3306 eq8237
    | exact resolve eq8237 eq3306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8237
  have eq9085 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 (M.op (M.op x y) (k X1 X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | exact superpose eq8933 eq2948
    | (have j1 := eq8933 (M.op X0 (M.op x y)) (M.op X1 (M.op (M.op x y) (k X1 X0)))
       grind)
    | exact resolve eq2948 eq8933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2948 eq8933
  have eq9248 : (k (τ (M.op x y)) (M.op x y)) = (k (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq30 eq5016
    | (have j0 := eq5016 (σ (M.op x y))
       grind)
    | exact resolve eq5016 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5016
  have eq9269 : (k (τ (M.op x y)) (M.op x y)) = (k (M.op x y) (τ (M.op x y))) := by
    first
    | (have r₁ := eq9248
       have r₂ := eq3281
       grind)
    | exact resolve eq9248 eq3281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9248
  have eq9420 : (k (σ (τ (M.op x y))) (σ (M.op x y))) = (σ (k (M.op x y) (τ (M.op x y)))) := by
    first
    | exact superpose eq9269 eq15
    | exact resolve eq15 eq9269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9426 : (k (σ (τ (M.op x y))) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (τ (M.op x y)))) := by
    first
    | (have i₁ := eq9420
       have i₂ := eq15 sF0 (τ sF0)
       grind)
    | exact superpose eq15 eq9420
    | exact resolve eq9420 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9420
  have eq9427 : (k (M.op x y) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq9426
       have i₂ := eq11 sF0
       grind)
    | exact superpose eq11 eq9426
    | exact resolve eq9426 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9426
  have eq9428 : (k (σ (M.op x y)) (M.op x y)) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq9427
    | exact resolve eq9427 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9427
  have eq10411 : (M.op x y) = (M.op (M.op x y) (M.op (k (M.op x y) (σ (M.op x y))) (M.op (M.op x y) (σ (M.op x y))))) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq9428 eq8389
    | (have j0 := eq8389 (M.op (M.op x y) (M.op (k (M.op x y) (σ (M.op x y))) (M.op (M.op x y) (σ (M.op x y)))))
       grind)
    | exact resolve eq8389 eq9428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8389
  have eq10505 : (M.op x y) = (M.op (M.op x y) (M.op (k (M.op x y) (σ (M.op x y))) (M.op (M.op x y) (σ (M.op x y))))) := by
    first
    | (have r₁ := eq10411
       have r₂ := eq3281
       grind)
    | exact resolve eq10411 eq3281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10411
  have eq10527 : (M.op (M.op x y) (k (M.op x y) (σ (M.op x y)))) = (M.op (M.op (M.op x y) (σ (M.op x y))) (M.op x y)) := by
    first
    | exact superpose eq10505 eq3508
    | exact resolve eq3508 eq10505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3508 eq10505
  have eq10578 : (M.op (M.op x y) (k (M.op x y) (σ (M.op x y)))) = (M.op (M.op x y) (M.op (σ (M.op x y)) (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq4479 eq10527
    | exact resolve eq10527 eq4479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4479 eq10527
  have eq10595 : (σ (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (σ (M.op x y)))) := by
    first
    | exact superpose eq5234 eq10578
    | exact resolve eq10578 eq5234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10578
  have eq10618 : (σ (M.op x y)) = (k (M.op x y) (k (M.op x y) (σ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq10595 eq3766
    | (have j0 := eq3766 (k (M.op x y) (σ (M.op x y)))
       grind)
    | exact resolve eq3766 eq10595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3766
  have eq11135 : (τ (σ (M.op x y))) = (k (τ (M.op x y)) (τ (k (M.op x y) (σ (M.op x y))))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq10618 eq72
    | exact resolve eq72 eq10618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10618
  have eq11162 : (τ (σ (M.op x y))) = (k (τ (M.op x y)) (k (τ (M.op x y)) (τ (σ (M.op x y))))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq11135
       have i₂ := eq72 sF1 sF0
       grind)
    | exact superpose eq72 eq11135
    | exact resolve eq11135 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq11135
  have eq11170 : (M.op x y) = (k (τ (M.op x y)) (k (τ (M.op x y)) (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq30 eq11162
    | exact resolve eq11162 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq11162
  have eq11177 : (M.op x y) = (k (τ (M.op x y)) (k (M.op x y) (τ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq9269 eq11170
    | exact resolve eq11170 eq9269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9269 eq11170
  have eq12622 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 (M.op (M.op x y) (k X1 X0)))) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3306 X0
       have i₂ := eq9085 X0 (M.op X0 sF0)
       grind)
    | exact superpose eq9085 eq3306
    | (have j1 := eq9085 (M.op (M.op x y) (M.op X1 (M.op (M.op x y) (k X1 X0)))) X0
       grind)
    | exact resolve eq3306 eq9085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3306 eq9085
  have eq15528 : (k (M.op x y) (τ (M.op x y))) = (M.op (M.op x y) (M.op (τ (M.op x y)) (M.op (M.op x y) (M.op x y)))) ∨ (τ (M.op x y)) = (k (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq11177 eq12622
    | (have j0 := eq12622 (k (M.op x y) (τ (M.op x y))) (M.op (M.op x y) (M.op (τ (M.op x y)) (M.op (M.op x y) (M.op x y))))
       grind)
    | exact resolve eq12622 eq11177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11177 eq12622
  have eq15534 : (τ (M.op x y)) = (k (M.op x y) (τ (M.op x y))) ∨ (τ (M.op x y)) = (k (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq5234 eq15528
    | exact resolve eq15528 eq5234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5234 eq15528
  have eq15535 : (τ (M.op x y)) = (k (M.op x y) (τ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by grind
  clear eq15534
  have eq15570 : (σ (τ (M.op x y))) = (k (σ (M.op x y)) (σ (τ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq15535 eq15
    | exact resolve eq15 eq15535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15535
  have eq15576 : (M.op x y) = (k (σ (M.op x y)) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq15570
       have i₂ := eq11 sF0
       grind)
    | exact superpose eq11 eq15570
    | exact resolve eq15570 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15570
  have eq15582 : (M.op x y) = (k (σ (M.op x y)) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq15576
    | exact resolve eq15576 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq15576
  have eq15584 : (M.op x y) = (k (M.op x y) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq9428 eq15582
    | exact resolve eq15582 eq9428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9428 eq15582
  have eq15585 : (M.op x y) = (k (M.op x y) (σ (M.op x y))) := by grind
  clear eq15584
  have eq15588 : (σ (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq15585 eq10595
    | exact resolve eq10595 eq15585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10595 eq15585
  have eq15777 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq15588
       have i₂ := eq2958 sF0
       grind)
    | exact superpose eq2958 eq15588
    | exact resolve eq15588 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2958 eq15588
  have eq15816 : False := by grind
  exact eq15816
