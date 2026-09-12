import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1489`: `x = (y ◇ x) ◇ (y ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation1489 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1489 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1489.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq88 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq89 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq93 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq89
  have eq94 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq93
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq95
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq95
    | exact resolve eq95 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq101
    | exact resolve eq101 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq102
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq684 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq72
    | (have j0 := eq72 X0 X1
       grind)
    | exact resolve eq72 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq72
  have eq770 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq684 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq7903 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7904 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq7903
    | exact resolve eq7903 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7903
  have eq7915 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq7904
       have r₂ := eq28
       grind)
    | exact resolve eq7904 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7904
  have eq7919 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq7915
    | exact resolve eq7915 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7915
  have eq7928 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (M.op (σ x) (σ y)) = (k (σ y) X0) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq7919 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq7919
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq7919
       grind)
    | exact resolve eq12 eq7919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7919
  have eq8442 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq7928
    | (have j0 := eq7928 (σ x)
       grind)
    | (have r₁ := eq7928 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq7928 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7928
  have eq8443 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq8442
  have eq8444 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq8443
  have eq8459 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq8444 eq103
    | exact resolve eq103 eq8444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq8444
  have eq8469 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq8459
  have eq8472 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8469
       have r₂ := eq28
       grind)
    | exact resolve eq8469 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8469
  have eq8475 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq8472
       grind)
    | exact superpose eq8472 eq94
    | exact resolve eq94 eq8472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8482 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = X0 ∨ (M.op x y) = (k y X0) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq12 y x
       have i₂ := eq8472
       grind)
    | exact superpose eq8472 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq8472
       grind)
    | exact resolve eq12 eq8472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8472
  have eq8510 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq8475
    | exact resolve eq8475 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8475
  have eq10829 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8482 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq8482
    | (have j0 := eq8482 x
       grind)
    | (have r₁ := eq8482 x
       have r₂ := eq19
       grind)
    | exact resolve eq8482 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8482
  have eq10830 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq10829
  have eq10831 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq10830
  have eq10844 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq770 x y
       have i₂ := eq10831
       grind)
    | exact superpose eq10831 eq770
    | (have j0 := eq770 x y
       grind)
    | exact resolve eq770 eq10831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq10831
  have eq10848 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10844
       have i₂ := eq94
       grind)
    | exact superpose eq94 eq10844
    | exact resolve eq10844 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10844
  have eq10858 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq10848
    | exact resolve eq10848 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10848
  have eq10863 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq10858
       have r₂ := eq8510
       grind)
    | exact resolve eq10858 eq8510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10858
  have eq10866 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10863
       have i₂ := eq94
       grind)
    | exact superpose eq94 eq10863
    | exact resolve eq10863 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq10863
  have eq10869 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10866
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10866
    | exact resolve eq10866 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10866
  have eq10872 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10869
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10869
    | exact resolve eq10869 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10869
  have eq10875 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq10872
    | exact resolve eq10872 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10872
  have eq10878 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10875
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10875
    | exact resolve eq10875 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10875
  have eq10881 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10878
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10878
    | exact resolve eq10878 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10878
  have eq10882 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10881
  have eq10943 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10882 eq8510
    | exact resolve eq8510 eq10882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8510 eq10882
  have eq10967 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq10943
  have eq10973 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq10967
       have r₂ := eq28
       grind)
    | exact resolve eq10967 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10967
  have eq10976 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq10973 eq30
    | exact resolve eq30 eq10973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq10973
  have eq11093 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq10976
    | exact resolve eq10976 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq10976
  have eq11094 : x = y := by grind
  clear eq11093
  have eq11113 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq11094
       grind)
    | exact superpose eq11094 eq19
    | exact resolve eq19 eq11094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq11114 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq11094
       grind)
    | exact superpose eq11094 eq25
    | exact resolve eq25 eq11094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq11094
  have eq11229 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq11114
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11114
    | exact resolve eq11114 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq11114
  have eq11252 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11229 eq27
    | exact resolve eq27 eq11229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq11229
  have eq11456 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq11252 eq71
    | exact resolve eq71 eq11252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq11252
  have eq11488 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq11456
       have i₂ := eq11113
       grind)
    | exact superpose eq11113 eq11456
    | exact resolve eq11456 eq11113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11113 eq11456
  have eq12666 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11488 eq15
    | exact resolve eq15 eq11488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11488
  have eq12713 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq12666
    | exact resolve eq12666 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq12666
  have eq12722 : False := by grind
  exact eq12722

/-- `Equation1560`: `x = (y ◇ z) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_y_pxy_pyx_Equation1560 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1560 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1560.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
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
  clear eq36
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
  have eq174 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
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
  have eq176 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y X0 x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X0 (M.op X3 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq16 X0 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X0) X1 X0
       have i₂ := eq16 X0 X0 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : (σ x) = (k (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq39 (M.op x x)
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq39
    | exact resolve eq39 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : (σ y) = (k (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq40 (M.op y y)
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq40
    | exact resolve eq40 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq186 : (σ y) = (k (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq183
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq183
    | exact resolve eq183 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq187 : (σ x) = (k (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq182
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq182
    | exact resolve eq182 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq194 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq175 (M.op y y)
       have i₂ := eq16 y y y
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (M.op X0 (M.op y X0)) = (M.op (M.op X1 (M.op x y)) (M.op (M.op X0 (M.op y X0)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : (σ y) = (k (σ (M.op (M.op x y) y)) (σ y)) := by
    first
    | (have i₁ := eq186
       have i₂ := eq194
       grind)
    | exact superpose eq194 eq186
    | exact resolve eq186 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq207 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq176 (M.op sF3 sF3)
       have i₂ := eq16 sF3 sF3 sF3
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 X1 : G, (M.op y (M.op x y)) = (M.op (M.op X0 (M.op X1 x)) (M.op (M.op y (M.op x y)) y)) := by
    intro X0 X1
    first
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X1 : G, (M.op y (M.op X1 (M.op (M.op y (M.op x y)) X1))) = X1 := by
    intro X1
    first
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : (τ (σ x)) = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | (have i₁ := eq141 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq141
    | exact resolve eq141 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq174
  have eq283 : x = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | exact superpose eq29 eq262
    | exact resolve eq262 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq642 : (k y y) = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq194
       grind)
    | exact superpose eq194 eq11
    | exact resolve eq11 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq650 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (k X0 X1) X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq181 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq181
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq181 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq677 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq685 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq686 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq685 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq698 : (k y y) = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) := by grind
  clear eq642
  have eq714 : (M.op x y) = (k y x) ∨ x = (M.op (M.op x y) y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq663
       have i₂ := eq194
       grind)
    | exact superpose eq194 eq663
    | exact resolve eq663 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq735 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq850 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq213 sF0
       have i₂ := eq181 sF0 y
       grind)
    | exact superpose eq181 eq213
    | exact resolve eq213 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq1041 : (M.op y y) = (M.op (k y y) y) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq698 eq181
    | exact resolve eq181 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1044 : y ≠ (k y y) ∨ y = (M.op (M.op x y) y) := by grind
  have eq1045 : (M.op (M.op x y) y) = (M.op (k y y) y) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq1041
       have i₂ := eq194
       grind)
    | exact superpose eq194 eq1041
    | exact resolve eq1041 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq1049 : (k y y) = (M.op (k y y) y) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq698 eq1045
    | exact resolve eq1045 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698 eq1045
  have eq2347 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op (M.op x y) y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq714
       grind)
    | exact superpose eq714 eq39
    | exact resolve eq39 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq2348 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op (M.op x y) y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2347
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2347
    | exact resolve eq2347 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2347
  have eq2350 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op (M.op x y) y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq2348
    | exact resolve eq2348 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2348
  have eq17840 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2350 eq677
    | exact resolve eq677 eq2350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2350
  have eq17849 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq17840
       have r₂ := eq27
       grind)
    | exact resolve eq17840 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17840
  have eq17856 : x = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17849 eq283
    | exact resolve eq283 eq17849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283 eq17849
  have eq17889 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq17856
    | exact resolve eq17856 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17856
  have eq17890 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y x) ∨ x = (M.op (M.op x y) y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq17889
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq17889
       have r₂ := eq13 y x
       grind)
    | exact resolve eq17889 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17889
  have eq17907 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op (M.op x y) y) := by
    first
    | exact superpose eq17890 eq181
    | exact resolve eq181 eq17890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17890
  have eq17915 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) y) := by
    first
    | exact superpose eq26 eq17907
    | exact resolve eq17907 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17907
  have eq17954 : x = (M.op x y) ∨ x = (M.op (M.op x y) y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq714
       have i₂ := eq17915
       grind)
    | exact superpose eq17915 eq714
    | exact resolve eq714 eq17915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714 eq17915
  have eq17959 : y = (M.op x x) ∨ x = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17954
  have eq18026 : y = (M.op y x) ∨ x = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq181 x x
       have i₂ := eq17959
       grind)
    | exact superpose eq17959 eq181
    | exact resolve eq181 eq17959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17959
  have eq18223 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq18026
       grind)
    | exact superpose eq18026 eq175
    | exact resolve eq175 eq18026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq18026
  have eq18248 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18223
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18223
    | exact resolve eq18223 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18223
  have eq18355 : x = (M.op (M.op x y) y) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18248 eq181
    | exact resolve eq181 eq18248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18248
  have eq18568 : (M.op x y) = (M.op y y) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18355 eq181
    | exact resolve eq181 eq18355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18578 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18568
       have i₂ := eq194
       grind)
    | exact superpose eq194 eq18568
    | exact resolve eq18568 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq18568
  have eq18585 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18578
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18578
    | exact resolve eq18578 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18578
  have eq18748 : x = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18585 eq18355
    | exact resolve eq18355 eq18585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18355 eq18585
  have eq18766 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18748
  have eq18777 : ∀ X0 : G, (M.op x (M.op X0 (M.op (M.op x y) X0))) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18766 eq16
    | exact resolve eq16 eq18766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18778 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) (M.op (M.op x y) x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18766 eq16
    | exact resolve eq16 eq18766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18782 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18766 eq181
    | exact resolve eq181 eq18766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18789 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18766 eq18782
    | exact resolve eq18782 eq18766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18766 eq18782
  have eq18793 : (M.op x y) = (M.op y (M.op (M.op x y) x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18789 eq850
    | exact resolve eq850 eq18789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq18804 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op (M.op x y) x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18789 eq16
    | exact resolve eq16 eq18789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19043 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op (M.op (M.op (M.op x y) x) (M.op x y)) (M.op (M.op x y) x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18793 eq195
    | exact resolve eq195 eq18793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq19054 : (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) = (M.op (M.op x y) (M.op (M.op x y) x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18793 eq181
    | exact resolve eq181 eq18793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18793
  have eq19067 : (M.op x y) = (M.op (M.op x y) (M.op (M.op x y) x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18778 eq19054
    | exact resolve eq19054 eq18778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19054
  have eq19070 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = (M.op (M.op (M.op x y) x) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18804 eq19043
    | exact resolve eq19043 eq18804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19043
  have eq19073 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) x) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19070 x
       have i₂ := eq181 sF0 x
       grind)
    | exact superpose eq181 eq19070
    | exact resolve eq19070 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19070
  have eq19075 : x = (M.op (M.op (M.op x y) x) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18789 eq19073
    | exact resolve eq19073 eq18789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19073
  have eq19086 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op (M.op (M.op (M.op x y) x) (M.op x y)) (M.op (M.op x y) x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq19067 eq180
    | exact resolve eq180 eq19067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq19102 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq18804 eq19086
    | exact resolve eq19086 eq18804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18804 eq19086
  have eq19107 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq19075 eq19102
    | exact resolve eq19102 eq19075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19102
  have eq19154 : (M.op (M.op x y) x) = (M.op x (M.op (M.op (M.op x y) x) (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19067 eq18777
    | exact resolve eq18777 eq19067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19067
  have eq19159 : (M.op x y) = (M.op x (M.op (M.op x y) x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18789 eq18777
    | exact resolve eq18777 eq18789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18777 eq18789
  have eq19190 : (M.op x y) = (M.op x (M.op (M.op x y) x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19159
  have eq19194 : (M.op (M.op x y) x) = (M.op x (M.op (M.op (M.op x y) x) (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19154
  have eq19203 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19075 eq19194
    | exact resolve eq19194 eq19075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19075 eq19194
  have eq19261 : (M.op x (M.op (M.op x y) x)) = (k x (M.op (M.op x y) x)) ∨ x = (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq735 x
       have i₂ := eq19203
       grind)
    | exact superpose eq19203 eq735
    | exact resolve eq735 eq19203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19291 : (M.op x (M.op (M.op x y) x)) = (k x (M.op (M.op x y) x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18778 eq19261
    | exact resolve eq19261 eq18778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18778 eq19261
  have eq19292 : (M.op x (M.op (M.op x y) x)) = (k x (M.op (M.op x y) x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19291
  have eq19294 : (M.op x y) = (k x (M.op (M.op x y) x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19190 eq19292
    | exact resolve eq19292 eq19190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19190 eq19292
  have eq19335 : (σ (M.op x y)) = (k (σ x) (σ (M.op (M.op x y) x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19294 eq35
    | exact resolve eq35 eq19294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq19294
  have eq19338 : (σ (M.op x y)) = (k (σ x) (σ (M.op (M.op x y) x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq19335
    | exact resolve eq19335 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19335
  have eq19731 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq178 eq19107
    | exact resolve eq19107 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19107
  have eq19777 : ∀ X0 : G, y = (M.op (M.op X0 x) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq19731 eq178
    | exact resolve eq178 eq19731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq19731
  have eq19812 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19777 x
       have i₂ := eq181 x x
       grind)
    | exact superpose eq181 eq19777
    | exact resolve eq19777 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19777
  have eq19819 : y = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19203
       have i₂ := eq19812
       grind)
    | exact superpose eq19812 eq19203
    | exact resolve eq19203 eq19812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19203
  have eq19820 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq187
       have i₂ := eq19812
       grind)
    | exact superpose eq19812 eq187
    | exact resolve eq187 eq19812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq19812
  have eq19849 : y = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19819
  have eq19865 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19820
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19820
    | exact resolve eq19820 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19820
  have eq19943 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19849 eq19338
    | exact resolve eq19338 eq19849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19338 eq19849
  have eq19968 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19943
  have eq19992 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19968
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19968
    | exact resolve eq19968 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19968
  have eq20218 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19865 eq677
    | exact resolve eq677 eq19865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677 eq19865
  have eq20226 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20218
  have eq21984 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20226 eq735
    | exact resolve eq735 eq20226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20226
  have eq22004 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21984
  have eq22013 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq22004
    | exact resolve eq22004 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22004
  have eq22016 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19992 eq22013
    | exact resolve eq22013 eq19992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19992 eq22013
  have eq22017 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22016
       have r₂ := eq27
       grind)
    | exact resolve eq22016 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22016
  have eq22037 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22017 eq181
    | exact resolve eq181 eq22017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22017
  have eq22048 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq22037
    | exact resolve eq22037 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22037
  have eq22049 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq22048
  have eq22058 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22049 eq207
    | exact resolve eq207 eq22049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq22070 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq22058
    | exact resolve eq22058 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22058
  have eq22071 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22049 eq22070
    | exact resolve eq22070 eq22049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22049 eq22070
  have eq22084 : ∀ X0 : G, (σ x) ≠ X0 ∨ (σ y) = (k X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22071 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq22071
       grind)
    | exact resolve eq13 eq22071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22085 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22071 eq11
    | exact resolve eq11 eq22071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22071
  have eq22099 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq22085
  have eq22223 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22099 eq115
    | exact resolve eq115 eq22099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22239 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq22223
    | exact resolve eq22223 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22223
  have eq22251 : x = (M.op x y) ∨ y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1049
       have i₂ := eq22239
       grind)
    | exact superpose eq22239 eq1049
    | exact resolve eq1049 eq22239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049 eq22239
  have eq22275 : x = (M.op x y) ∨ y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22251
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22251
    | exact resolve eq22251 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22251
  have eq22276 : y = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq22275
  have eq22290 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22276 eq197
    | exact resolve eq197 eq22276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22276
  have eq22358 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22290
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22290
    | exact resolve eq22290 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq22290
  have eq22373 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq22084 (σ y)
       grind)
    | (have r₁ := eq22358
       have r₂ := eq22084 (σ y)
       grind)
    | exact resolve eq22358 eq22084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22084 eq22358
  have eq22399 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22373 eq22099
    | exact resolve eq22099 eq22373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22099
  have eq22401 : (τ (σ y)) = (k (τ (σ y)) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22373 eq152
    | exact resolve eq152 eq22373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq22373
  have eq22413 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq22399
  have eq22422 : y = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq22401
    | exact resolve eq22401 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22401
  have eq22429 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22413 eq31
    | exact resolve eq31 eq22413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq22447 : (k y y) = (τ (k (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22413 eq115
    | exact resolve eq115 eq22413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq22413
  have eq22580 : (k x x) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq97 eq22447
    | exact resolve eq22447 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq22447
  have eq22598 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq22429
    | exact resolve eq22429 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq22429
  have eq22613 : y = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22422 eq22580
    | exact resolve eq22580 eq22422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22580
  have eq22625 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22598 eq22613
    | exact resolve eq22613 eq22598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22613
  have eq22821 : y ≠ y ∨ y = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1044
       have i₂ := eq22422
       grind)
    | exact superpose eq22422 eq1044
    | (have r₁ := eq1044
       have r₂ := eq22422
       grind)
    | exact resolve eq1044 eq22422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044 eq22422
  have eq22841 : y = (M.op (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq22821
  have eq22855 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22598 eq22841
    | exact resolve eq22841 eq22598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22841
  have eq23357 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq686 x
       have i₂ := eq22625
       grind)
    | exact superpose eq22625 eq686
    | (have j0 := eq686 x
       grind)
    | (have r₁ := eq686 x
       have r₂ := eq22625
       grind)
    | exact resolve eq686 eq22625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686 eq22625
  have eq23362 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq23357
  have eq23395 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op (M.op X0 x) (M.op (M.op y (M.op x y)) y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22855 eq212
    | exact resolve eq212 eq22855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq23403 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22855 eq16
    | exact resolve eq16 eq22855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23444 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23362 eq23403
    | exact resolve eq23403 eq23362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23403
  have eq23445 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op X0 x) (M.op (M.op x (M.op x y)) x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22598 eq23395
    | exact resolve eq23395 eq22598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22598 eq23395
  have eq23448 : ∀ X0 : G, (M.op (M.op X0 x) x) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23444 eq23445
    | exact resolve eq23445 eq23444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23444 eq23445
  have eq23449 : (M.op x x) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23448 x
       have i₂ := eq181 x x
       grind)
    | exact superpose eq181 eq23448
    | exact resolve eq23448 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23448
  have eq23450 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23362 eq23449
    | exact resolve eq23449 eq23362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23449
  have eq23588 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) (M.op (M.op x y) x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23450 eq16
    | exact resolve eq16 eq23450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23450
  have eq23615 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq22855 eq23588
    | exact resolve eq23588 eq22855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22855 eq23588
  have eq23625 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23615 x
       have i₂ := eq181 x x
       grind)
    | exact superpose eq181 eq23615
    | exact resolve eq23615 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23615
  have eq23745 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23362
       have i₂ := eq23625
       grind)
    | exact superpose eq23625 eq23362
    | exact resolve eq23362 eq23625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23362 eq23625
  have eq23781 : x = (M.op x y) := by grind
  clear eq23745
  have eq23802 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq23781
       grind)
    | exact superpose eq23781 eq18
    | exact resolve eq18 eq23781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq23803 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq23781
       grind)
    | exact superpose eq23781 eq22
    | exact resolve eq22 eq23781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq23781
  have eq23858 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq23803 eq20
    | exact resolve eq20 eq23803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23803
  have eq24296 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq23802 eq197
    | exact resolve eq197 eq23802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq23802
  have eq24340 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq24296
    | exact resolve eq24296 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq24296
  have eq24344 : (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq23858 eq24340
    | exact resolve eq24340 eq23858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24340
  have eq24378 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq24344 eq650
    | (have j0 := eq650 (σ x) (σ y)
       grind)
    | exact resolve eq650 eq24344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq24382 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq11 eq24378
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq24378 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24378
  have eq24388 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq24344 eq24382
    | exact resolve eq24382 eq24344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24382
  have eq24389 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq24388
  have eq27172 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq24389 eq735
    | exact resolve eq735 eq24389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq27183 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq24389 eq181
    | exact resolve eq181 eq24389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24389
  have eq27192 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq27172
  have eq27201 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq24344 eq27192
    | exact resolve eq27192 eq24344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24344 eq27192
  have eq27205 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq27201
    | exact resolve eq27201 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27201
  have eq27439 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27183 eq176
    | exact resolve eq176 eq27183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq27183
  have eq27472 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq27439
    | exact resolve eq27439 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27439
  have eq27478 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27205 eq27472
    | exact resolve eq27472 eq27205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27205 eq27472
  have eq27479 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq27478
  have eq27503 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27479 eq181
    | exact resolve eq181 eq27479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq27479
  have eq27522 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27503 eq26
    | exact resolve eq26 eq27503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq27503
  have eq27545 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq27522 eq27
    | exact resolve eq27 eq27522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq27522
  have eq27570 : False := by grind
  exact eq27570

/-- `Equation1577`: `x = (y ◇ z) ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pxx_pyx_pxy_Equation1577 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1577 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1577.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (M.op X2 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op x y) (M.op x (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) (M.op (M.op X1 (M.op X2 X0)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op X1 X2) (M.op X1 (M.op X2 X0))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op (M.op X1 X2) X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X0) (M.op X1 X2) X1
       have i₂ := eq14 X0 X1 X2
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
  have eq71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq69 (σ X0)
       grind)
    | exact superpose eq69 eq10
    | exact resolve eq10 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq69 sF2
       grind)
    | exact superpose eq69 eq49
    | exact resolve eq49 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq74 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq73
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq73
    | exact resolve eq73 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq71
    | exact resolve eq71 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op y y) = (M.op y x) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op y y) = (M.op y x) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op y y) = (M.op y x) := by
    first
    | exact superpose eq20 eq89
    | exact resolve eq89 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq92 : (M.op y y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq107 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq111 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq107
       have i₂ := eq69 sF3
       grind)
    | exact superpose eq69 eq107
    | exact resolve eq107 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq113 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq111
       have i₂ := eq69 y
       grind)
    | exact superpose eq69 eq111
    | exact resolve eq111 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq137 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq140 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq137
       have i₂ := eq69 sF1
       grind)
    | exact superpose eq69 eq137
    | exact resolve eq137 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq142 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq140
       have i₂ := eq69 sF0
       grind)
    | exact superpose eq69 eq140
    | exact resolve eq140 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq147 : ∀ X0 : G, (σ (k X0 (M.op y y))) = (k (σ X0) (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (M.op y y)
       have i₂ := eq113
       grind)
    | exact superpose eq113 eq10
    | exact resolve eq10 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq142 eq16
    | exact resolve eq16 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : ∀ X0 X1 : G, (M.op x (M.op y X0)) = (M.op (M.op X1 (M.op x y)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) (M.op (M.op x (M.op y X0)) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (M.op (σ y) X0)) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op X0 (σ x)) (M.op (M.op X0 (M.op (σ x) (σ y))) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : y = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq53 eq239
    | exact resolve eq239 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op x X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq239 (M.op sF0 (M.op x X0))
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq239
    | exact resolve eq239 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq438 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 y) (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq412 eq14
    | exact resolve eq14 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq441 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) X3) = (M.op (M.op X0 (M.op X1 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X3 (M.op X1 X2) (M.op X1 (M.op X2 X0))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq450 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op (σ y) X0)) X1) = (M.op (M.op X0 (M.op (σ x) (σ y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq51 eq56
    | exact resolve eq56 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq451 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq239 eq56
    | exact resolve eq56 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq452 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 (M.op X1 X0) X1
       have i₂ := eq56 (M.op X1 X0) X1 X0
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (M.op (M.op X2 X1) (M.op X2 X0)) X2 X1
       have i₂ := eq14 X0 (M.op X2 X1) X2
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454 : ∀ X0 : G, y = (M.op X0 (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq455 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op (σ x) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq54 eq244
    | exact resolve eq244 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ y)) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq481 eq14
    | exact resolve eq14 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq537 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X0) X3)) (M.op (M.op X2 (M.op X0 X1)) X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X1 X2 (M.op (M.op X3 X0) X3) X4
       have i₂ := eq56 X1 X3 X0
       grind)
    | exact superpose eq56 eq52
    | exact resolve eq52 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq538 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X3 (M.op X1 X2)) (M.op (M.op X3 X0) X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X1 (M.op X2 X0)) X3 (M.op X1 X2) X4
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X1 (M.op (M.op X2 X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X1 X2 X3 (M.op X2 (M.op (M.op X3 X1) X0))
       have i₂ := eq14 X0 X2 (M.op X3 X1)
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X1 X2 X3 (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X2 X3))) X0)
       have i₂ := eq52 (M.op X2 X3) X2 (M.op X3 X1) X0
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) (M.op (M.op X3 (M.op X4 X2)) X0)) = (M.op (M.op X1 X2) (M.op X1 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op (M.op X3 X4) (M.op (M.op X3 (M.op X4 X2)) X0)) X1 X2
       have i₂ := eq52 X2 X3 X4 X0
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq599 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x X0)) y) := by
    intro X0
    first
    | exact superpose eq454 eq14
    | exact resolve eq14 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq638 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op (M.op (M.op X2 X3) (M.op (M.op X2 (M.op X3 X1)) X0)) X4)) = (M.op (M.op X5 X0) (M.op X5 X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 X4 X5 X1 (M.op (M.op X2 X3) (M.op (M.op X2 (M.op X3 X1)) X0))
       have i₂ := eq52 X1 X2 X3 X0
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op y (M.op (M.op X0 x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq662 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op (σ y) (M.op (M.op X0 (σ x)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq667 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op x (M.op (M.op y X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq50 eq55
    | exact resolve eq55 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq676 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 (M.op X4 X0)))) = (M.op (M.op (M.op X3 X4) (M.op X1 X2)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op X3 (M.op X4 X0)) (M.op X3 X4) X1 X2
       have i₂ := eq14 X0 X3 X4
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op (M.op x (M.op X0 X1)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 y x X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55
    | (have j0 := eq55 y x X0 X1
       grind)
    | exact resolve eq55 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq685 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op (M.op (σ x) (M.op X0 X1)) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq55
    | (have j0 := eq55 (σ y) (σ x) X0 X1
       grind)
    | exact resolve eq55 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq688 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X1 X2) X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 (M.op (M.op X1 X2) X0) x X1 X2
       have i₂ := eq14 X0 x (M.op X1 X2)
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq689 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op X0 (M.op (M.op (M.op X1 X2) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X3 (M.op (M.op X1 X2) X0) X1 X2
       have i₂ := eq56 (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X2) X0
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X1 (M.op (M.op X3 X0) (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X1 X3 X0 (M.op X3 X2)
       have i₂ := eq55 X2 X3 X0 X1
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq704 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X2) X4) = (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X0 X1))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 X4 (M.op X3 (M.op X0 X1)) (M.op X3 X2)
       have i₂ := eq55 X2 X3 X0 X1
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq807 : ∀ X0 : G, (M.op x (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq451 (M.op y (M.op sF0 X0))
       have i₂ := eq14 X0 y sF0
       grind)
    | exact superpose eq14 eq451
    | exact resolve eq451 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq1016 : ∀ X0 : G, y = (M.op X0 (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq52 X0 X0 x y
       have i₂ := eq599 X0
       grind)
    | exact superpose eq599 eq52
    | exact resolve eq52 eq599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq599
  have eq1462 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq142 eq76
    | exact resolve eq76 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1467 : (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) = (σ (M.op (k x x) (k x x))) := by
    first
    | (have i₁ := eq76 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq76
    | exact resolve eq76 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq76
  have eq1497 : (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq1467
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq1467
    | exact resolve eq1467 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467
  have eq1499 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq1497
       have i₂ := eq69 sF2
       grind)
    | exact superpose eq69 eq1497
    | exact resolve eq1497 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497
  have eq2098 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq454 eq452
    | exact resolve eq452 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2099 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq455 eq452
    | exact resolve eq452 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq2505 : ∀ X0 X1 : G, (M.op x (M.op y X0)) = (M.op X1 (M.op (M.op (M.op x y) X1) X0)) := by
    intro X0 X1
    first
    | exact superpose eq50 eq453
    | exact resolve eq453 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2522 : ∀ X0 : G, (M.op (M.op x y) (M.op y (M.op x X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2098 eq453
    | exact resolve eq453 eq2098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2098
  have eq2541 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X1 (M.op X1 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq452 (M.op X1 X0) (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq453 X0 (M.op X1 X0) X1
       grind)
    | exact superpose eq453 eq452
    | exact resolve eq452 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq3461 : ∀ X0 : G, (M.op y (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op (M.op x (M.op y x)) X0)) := by
    intro X0
    first
    | exact superpose eq243 eq413
    | exact resolve eq413 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq3482 : ∀ X0 : G, (M.op y (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq3461 X0
       have i₂ := eq452 x y X0
       grind)
    | exact superpose eq452 eq3461
    | exact resolve eq3461 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3461
  have eq4311 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (σ x)) (M.op (M.op X1 (M.op (σ x) (σ y))) X0)) X2) = (M.op (M.op X0 (σ y)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq258 eq56
    | exact resolve eq56 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq6429 : (M.op y (M.op x y)) = (M.op (M.op x x) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq454 eq682
    | exact resolve eq682 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6431 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op x y) (M.op (M.op (M.op x (M.op y x)) X0) y)) := by
    intro X0
    first
    | exact superpose eq243 eq682
    | exact resolve eq682 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq6453 : ∀ X0 X1 : G, (M.op x (M.op y (M.op x y))) = (M.op (M.op X0 (M.op X1 y)) (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | exact superpose eq682 eq242
    | exact resolve eq242 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242 eq682
  have eq6462 : ∀ X1 : G, (M.op x (M.op y (M.op x y))) = (M.op X1 (M.op y (M.op X1 y))) := by
    intro X1
    first
    | (have i₁ := eq6453 x X1
       have i₂ := eq55 (M.op X1 y) x X1 y
       grind)
    | exact superpose eq55 eq6453
    | exact resolve eq6453 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6453
  have eq6469 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op x y) (M.op (M.op y X0) y)) := by
    intro X0
    first
    | (have i₁ := eq6431 X0
       have i₂ := eq452 x y X0
       grind)
    | exact superpose eq452 eq6431
    | exact resolve eq6431 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452 eq6431
  have eq6790 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq450 eq685
    | exact resolve eq685 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8115 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X1 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2541 X0 X1 (M.op X1 X2)
       have i₂ := eq55 X2 X1 X1 X0
       grind)
    | exact superpose eq55 eq2541
    | exact resolve eq2541 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8139 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 X1 (M.op X1 X0)
       have i₂ := eq2541 X0 X1 X1
       grind)
    | exact superpose eq2541 eq56
    | exact resolve eq56 eq2541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq15317 : ∀ X0 X1 : G, (M.op X1 (M.op (σ y) X0)) = (M.op (σ x) (M.op (M.op X1 (M.op (σ x) (σ y))) X0)) := by
    intro X0 X1
    first
    | exact superpose eq244 eq561
    | exact resolve eq561 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq15754 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X1) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq688 X2 X1 X0
       have i₂ := eq561 X2 X0 X0 X1
       grind)
    | (have i₁ := eq688 X0 X2 x
       have i₂ := eq561 X0 x X2 x
       grind)
    | exact superpose eq561 eq688
    | exact resolve eq688 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16975 : (M.op (M.op x y) y) = (M.op x (M.op x (M.op y (M.op x y)))) := by
    first
    | exact superpose eq6429 eq688
    | exact resolve eq688 eq6429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6429
  have eq17508 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X1 X0) X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq566 X2 X1 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq14 X0 (M.op X1 X0) X1
       grind)
    | exact superpose eq14 eq566
    | exact resolve eq566 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq18889 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op y (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0
    first
    | (have i₁ := eq6469 x
       have i₂ := eq561 y x sF0 y
       grind)
    | (have i₁ := eq6469 x
       have i₂ := eq561 y sF0 y x
       grind)
    | exact superpose eq561 eq6469
    | exact resolve eq6469 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6469
  have eq22925 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq688 (M.op X0 (M.op X0 X1)) X2 X0
       have i₂ := eq693 X0 X0 X1 X2
       grind)
    | exact superpose eq693 eq688
    | exact resolve eq688 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688 eq693
  have eq24497 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) (M.op X0 (σ y))))) := by
    intro X0
    first
    | exact superpose eq6790 eq15754
    | exact resolve eq15754 eq6790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6790
  have eq29779 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq481 eq22925
    | exact resolve eq22925 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481 eq22925
  have eq53102 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op (M.op (M.op X0 X1) (M.op X2 (M.op (M.op X3 X0) X3))) X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq537 X0 X1 X2 X3 X4
       have i₂ := eq561 X4 (M.op X2 (M.op (M.op X3 X0) X3)) X2 (M.op X0 X1)
       grind)
    | (have i₁ := eq537 X0 X1 X3 X3 X0
       have i₂ := eq561 X0 (M.op X0 X1) (M.op X3 (M.op (M.op X3 X0) X3)) X3
       grind)
    | exact superpose eq561 eq537
    | exact resolve eq537 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq53438 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op (M.op (M.op X1 (M.op X2 X0)) X3) (M.op (M.op X3 X0) X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq538 X0 X1 X2 X3 X4
       have i₂ := eq561 (M.op (M.op X3 X0) X4) (M.op X1 X2) (M.op X1 (M.op X2 X0)) X3
       grind)
    | (have i₁ := eq538 X0 X1 X2 X2 X4
       have i₂ := eq561 (M.op (M.op X2 X0) X4) (M.op X1 (M.op X2 X0)) X2 (M.op X1 X2)
       grind)
    | exact superpose eq561 eq538
    | exact resolve eq538 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq53439 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op X0 (M.op (M.op (M.op (M.op X1 (M.op X2 X0)) X3) X3) X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53438 X0 X1 X2 X3 X4
       have i₂ := eq561 X4 X0 (M.op (M.op X1 (M.op X2 X0)) X3) X3
       grind)
    | (have i₁ := eq53438 X3 X1 X2 X2 X0
       have i₂ := eq561 X0 (M.op (M.op X1 (M.op X2 X3)) X2) X2 X3
       grind)
    | exact superpose eq561 eq53438
    | exact resolve eq53438 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53438
  have eq53440 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X2) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X4))) = X4 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq53439 X0 X1 X2 x X4
       have i₂ := eq17508 x (M.op X1 (M.op X2 X0)) X4
       grind)
    | exact superpose eq17508 eq53439
    | exact resolve eq53439 eq17508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17508 eq53439
  have eq54057 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X3) X0)) = (M.op (M.op X1 X2) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53440 X3 X1 X2 (M.op X1 (M.op (M.op X2 X3) X0))
       have i₂ := eq14 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq14 eq53440
    | exact resolve eq53440 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53440
  have eq56073 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op X1 X0)) = (M.op X3 (M.op (M.op (M.op X4 X2) (M.op X3 X4)) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq574 X0 X1 X2 X3 X4
       have i₂ := eq561 X0 (M.op X3 X4) X3 (M.op X4 X2)
       grind)
    | (have i₁ := eq574 X0 X1 X2 X3 X4
       have i₂ := eq561 X0 (M.op X4 X2) (M.op X3 X4) X3
       grind)
    | exact superpose eq561 eq574
    | exact resolve eq574 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq56074 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op X1 X0)) = (M.op X3 (M.op (M.op X4 (M.op (M.op X4 X2) X3)) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56073 X0 X1 X2 X3 X4
       have i₂ := eq441 X4 (M.op X4 X2) X3 X0
       grind)
    | (have i₁ := eq56073 X3 X1 X2 X1 X2
       have i₂ := eq441 (M.op X2 X2) X1 X2 X3
       grind)
    | exact superpose eq441 eq56073
    | exact resolve eq56073 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56073
  have eq63108 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X2) X4) = (M.op (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X2)) X3)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq704 X0 X1 X2 X3 X4
       have i₂ := eq441 (M.op X0 X1) (M.op X0 (M.op X1 X2)) X3 X4
       grind)
    | (have i₁ := eq704 X0 X1 X2 X1 X3
       have i₂ := eq441 (M.op X0 (M.op X1 X2)) X1 (M.op X0 X1) X3
       grind)
    | exact superpose eq441 eq704
    | exact resolve eq704 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441 eq704
  have eq63109 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X2) X4) = (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X0 (M.op X1 X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq63108 X0 X1 X2 X3 X4
       have i₂ := eq676 X4 (M.op X0 (M.op X1 X2)) X3 X0 X1
       grind)
    | exact superpose eq676 eq63108
    | exact resolve eq63108 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63108
  have eq70637 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X2 (M.op (M.op (M.op X3 X0) X3) (M.op X0 (M.op X1 X4)))))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53102 X0 X1 X2 X3 X4
       have i₂ := eq676 X4 X2 (M.op (M.op X3 X0) X3) X0 X1
       grind)
    | exact superpose eq676 eq53102
    | exact resolve eq53102 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53102
  have eq70638 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X2 (M.op (M.op X3 (M.op X3 X0)) (M.op X0 (M.op X1 X4)))))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq70637 X0 X1 X2 X3 X4
       have i₂ := eq8139 X3 (M.op X3 X0) (M.op X0 (M.op X1 X4))
       grind)
    | (have i₁ := eq70637 X0 X1 X2 X3 X4
       have i₂ := eq8139 (M.op X3 X0) X3 (M.op X0 (M.op X1 X4))
       grind)
    | exact superpose eq8139 eq70637
    | exact resolve eq70637 eq8139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70637
  have eq70639 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X2 (M.op X2 (M.op X0 (M.op X0 (M.op X1 X4)))))) = X4 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq70638 X0 X1 X2 x X4
       have i₂ := eq2541 X0 x (M.op X0 (M.op X1 X4))
       grind)
    | exact superpose eq2541 eq70638
    | exact resolve eq70638 eq2541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70638
  have eq71128 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X2 (M.op X0 X1)) (M.op X0 (M.op X1 (M.op X2 (M.op X3 X4)))))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq70639 X2 X3 (M.op X2 (M.op X0 X1)) X4
       have i₂ := eq55 (M.op X2 (M.op X3 X4)) X2 X0 X1
       grind)
    | exact superpose eq55 eq70639
    | exact resolve eq70639 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71374 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op X1 (M.op (M.op X2 (M.op X2 (M.op X3 (M.op X3 (M.op X1 X0))))) (σ y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq685 X1 (M.op X2 (M.op X2 (M.op X3 (M.op X3 (M.op X1 X0)))))
       have i₂ := eq70639 X3 X1 X2 X0
       grind)
    | exact superpose eq70639 eq685
    | exact resolve eq685 eq70639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq71726 : ∀ X0 X1 X3 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op X1 (M.op (M.op X3 (M.op X3 (M.op X1 X0))) (σ y))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq71374 X0 X1 X1 X3
       have i₂ := eq2541 (M.op X3 (M.op X3 (M.op X1 X0))) X1 sF3
       grind)
    | exact superpose eq2541 eq71374
    | exact resolve eq71374 eq2541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71374
  have eq71891 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op (M.op X2 (M.op X0 X1)) (M.op X1 (M.op X2 (M.op X3 X4)))))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq71128 X0 X1 X2 X3 X4
       have i₂ := eq8115 (M.op X2 (M.op X0 X1)) X0 (M.op X1 (M.op X2 (M.op X3 X4)))
       grind)
    | (have i₁ := eq71128 X0 X1 X2 X3 X4
       have i₂ := eq8115 X0 (M.op X2 (M.op X0 X1)) (M.op X1 (M.op X2 (M.op X3 X4)))
       grind)
    | exact superpose eq8115 eq71128
    | exact resolve eq71128 eq8115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71128
  have eq72233 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op X1 (M.op (M.op X1 X0) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq71726 X0 X1 X1
       have i₂ := eq2541 (M.op X1 X0) X1 sF3
       grind)
    | exact superpose eq2541 eq71726
    | exact resolve eq71726 eq2541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2541 eq71726
  have eq72333 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X1 (M.op (M.op X2 (M.op X0 X1)) (M.op X2 (M.op X3 X4)))))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq71891 X0 X1 X2 X3 X4
       have i₂ := eq8115 (M.op X2 (M.op X0 X1)) X1 (M.op X2 (M.op X3 X4))
       grind)
    | (have i₁ := eq71891 X0 X1 X2 X3 X4
       have i₂ := eq8115 X1 (M.op X2 (M.op X0 X1)) (M.op X2 (M.op X3 X4))
       grind)
    | exact superpose eq8115 eq71891
    | exact resolve eq71891 eq8115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71891
  have eq72546 : ∀ X0 X1 X3 X4 : G, (M.op X3 (M.op X0 (M.op X1 (M.op X0 (M.op X1 (M.op X3 X4)))))) = X4 := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq72333 X0 X1 x X3 X4
       have i₂ := eq55 (M.op X3 X4) x X0 X1
       grind)
    | exact superpose eq55 eq72333
    | exact resolve eq72333 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72333
  have eq75248 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X1 X2) X0)) = (M.op X3 (M.op (M.op X4 (M.op (M.op X4 X2) X3)) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56074 X0 X1 X2 X3 X4
       have i₂ := eq8115 (M.op X1 X2) X1 X0
       grind)
    | (have i₁ := eq56074 X0 X1 X2 X3 X4
       have i₂ := eq8115 X1 (M.op X1 X2) X0
       grind)
    | exact superpose eq8115 eq56074
    | exact resolve eq56074 eq8115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56074
  have eq90335 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y X1)) = (M.op X0 (M.op (M.op X0 x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq454 eq75248
    | exact resolve eq75248 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454 eq75248
  have eq91465 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) X1)) = (M.op X0 (M.op (M.op X0 x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq3482 eq90335
    | exact resolve eq90335 eq3482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90335
  have eq98882 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op (M.op (M.op X2 X3) (M.op (M.op X2 (M.op X3 X1)) X0)) X4)) = (M.op X5 (M.op (M.op X5 X0) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq638 X0 X1 X2 X3 X4 X5
       have i₂ := eq8115 (M.op X5 X0) X5 X4
       grind)
    | (have i₁ := eq638 X0 X1 X2 X3 X4 X5
       have i₂ := eq8115 X5 (M.op X5 X0) X4
       grind)
    | exact superpose eq8115 eq638
    | exact resolve eq638 eq8115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq98883 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 (M.op (M.op X5 X0) X4)) = (M.op X1 (M.op (M.op X2 (M.op X3 X1)) (M.op X0 (M.op X2 (M.op X3 X4))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq98882 X0 X1 X2 X3 X4 X5
       have i₂ := eq676 X4 (M.op X2 (M.op X3 X1)) X0 X2 X3
       grind)
    | exact superpose eq676 eq98882
    | exact resolve eq98882 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98882
  have eq98884 : ∀ X0 X1 X4 X5 : G, (M.op X1 (M.op (M.op X0 X1) X4)) = (M.op X5 (M.op (M.op X5 X0) X4)) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq98883 X0 X1 x x X4 X5
       have i₂ := eq63109 x x X1 X0 X4
       grind)
    | exact superpose eq63109 eq98883
    | exact resolve eq98883 eq63109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63109 eq98883
  have eq99660 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X0 (M.op X1 X2))) = (M.op X3 (M.op (M.op (M.op X0 X1) X3) (M.op X4 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq98884 (M.op X0 X1) X3 (M.op X4 X2) X4
       have i₂ := eq55 X2 X4 X0 X1
       grind)
    | exact superpose eq55 eq98884
    | exact resolve eq98884 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq99874 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op x X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq98884 x X1 X0 y
       have i₂ := eq661 y X0
       grind)
    | exact superpose eq661 eq98884
    | exact resolve eq98884 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq99879 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (M.op (M.op (σ x) X1) X0)) := by
    intro X0 X1
    first
    | exact superpose eq662 eq98884
    | exact resolve eq98884 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662 eq98884
  have eq100962 : ∀ X0 X1 X2 X4 : G, (M.op X4 (M.op X0 (M.op X1 X2))) = (M.op X0 (M.op X1 (M.op X4 X2))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq99660 X0 X1 X2 x X4
       have i₂ := eq689 x X0 X1 (M.op X4 X2)
       grind)
    | exact superpose eq689 eq99660
    | exact resolve eq99660 eq689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689 eq99660
  have eq223033 : (σ (k (M.op y y) (M.op y y))) = (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq147 (M.op y y)
       have i₂ := eq113
       grind)
    | exact superpose eq113 eq147
    | exact resolve eq147 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq147
  have eq223136 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (k (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq223033
       have i₂ := eq69 (M.op sF3 sF3)
       grind)
    | exact superpose eq69 eq223033
    | exact resolve eq223033 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223033
  have eq223145 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq223136
       have i₂ := eq69 (M.op y y)
       grind)
    | exact superpose eq69 eq223136
    | exact resolve eq223136 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq223136
  have eq223149 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq223145
       have i₂ := eq438 y
       grind)
    | exact superpose eq438 eq223145
    | exact resolve eq223145 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438 eq223145
  have eq223150 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq510 eq223149
    | exact resolve eq223149 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510 eq223149
  have eq223151 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq142 eq223150
    | exact resolve eq223150 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq223150
  have eq223159 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq223151 eq29779
    | exact resolve eq29779 eq223151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29779
  have eq313631 : ∀ X0 : G, (M.op x (M.op x (M.op y (M.op x y)))) = (M.op X0 (M.op (M.op x y) (M.op y (M.op (M.op y X0) y)))) := by
    intro X0
    first
    | (have i₁ := eq667 X0 (M.op y (M.op (M.op y X0) y))
       have i₂ := eq6462 (M.op y X0)
       grind)
    | exact superpose eq6462 eq667
    | exact resolve eq667 eq6462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667 eq6462
  have eq313983 : ∀ X0 : G, (M.op x (M.op x (M.op y (M.op x y)))) = (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op y X0) y)))) := by
    intro X0
    first
    | exact superpose eq3482 eq313631
    | exact resolve eq313631 eq3482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3482 eq313631
  have eq314399 : ∀ X0 : G, (M.op x (M.op x (M.op y (M.op x y)))) = (M.op X0 (M.op y (M.op y (M.op (M.op X0 (M.op x y)) y)))) := by
    intro X0
    first
    | (have i₁ := eq313983 x
       have i₂ := eq561 y x sF0 y
       grind)
    | (have i₁ := eq313983 x
       have i₂ := eq561 y sF0 y x
       grind)
    | exact superpose eq561 eq313983
    | exact resolve eq313983 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313983
  have eq314727 : ∀ X0 : G, (M.op x (M.op x (M.op y (M.op x y)))) = (M.op X0 (M.op y (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq18889 eq314399
    | exact resolve eq314399 eq18889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18889 eq314399
  have eq314978 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op y (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq16975 eq314727
    | exact resolve eq314727 eq16975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16975 eq314727
  have eq470552 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op x (M.op y (M.op (M.op (M.op x y) X0) (M.op (σ (M.op x y)) (σ (M.op x y)))))) := by
    intro X0
    first
    | exact superpose eq223159 eq2505
    | exact resolve eq2505 eq223159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223159
  have eq471022 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op x (M.op y (M.op (σ (M.op x y)) (M.op (M.op (M.op x y) X0) (σ (M.op x y)))))) := by
    intro X0
    first
    | (have i₁ := eq470552 X0
       have i₂ := eq8115 (M.op sF0 X0) sF1 sF1
       grind)
    | (have i₁ := eq470552 X0
       have i₂ := eq8115 sF1 (M.op sF0 X0) sF1
       grind)
    | exact superpose eq8115 eq470552
    | exact resolve eq470552 eq8115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8115 eq470552
  have eq471469 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op x (M.op y (M.op (M.op x y) (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y)))))) := by
    intro X0
    first
    | (have i₁ := eq471022 x
       have i₂ := eq561 sF1 x sF1 sF0
       grind)
    | (have i₁ := eq471022 x
       have i₂ := eq561 sF1 sF1 sF0 x
       grind)
    | exact superpose eq561 eq471022
    | exact resolve eq471022 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561 eq471022
  have eq471763 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq807 eq471469
    | exact resolve eq471469 eq807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807 eq471469
  have eq723181 : ∀ X0 X1 : G, y = (M.op y (M.op X0 (M.op X0 (M.op X1 (M.op X1 (M.op y x)))))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq70639 X1 y X0 y
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq70639
    | exact resolve eq70639 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq723230 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq723181 x x
       have i₂ := eq70639 x y x x
       grind)
    | (have i₁ := eq723181 x x
       have i₂ := eq70639 x x x (M.op y (M.op x (M.op x (M.op x (M.op x (M.op y x))))))
       grind)
    | exact superpose eq70639 eq723181
    | exact resolve eq723181 eq70639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723181
  have eq723647 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq723230 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq723230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723230
  have eq723648 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq723647
    | exact resolve eq723647 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723647
  have eq723653 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq723648
       have r₂ := eq27
       grind)
    | exact resolve eq723648 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723648
  have eq723655 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq723653
    | exact resolve eq723653 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq723653
  have eq723856 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X0 (M.op X1 (M.op X1 (M.op (σ y) (σ x))))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq723655 eq70639
    | exact resolve eq70639 eq723655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723655
  have eq723905 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq723856 x x
       have i₂ := eq70639 x sF3 x sF2
       grind)
    | (have i₁ := eq723856 x x
       have i₂ := eq70639 x x x (M.op sF3 (M.op x (M.op x (M.op x (M.op x (M.op sF3 sF2))))))
       grind)
    | exact superpose eq70639 eq723856
    | exact resolve eq723856 eq70639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70639 eq723856
  have eq724341 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (M.op (M.op (σ x) (M.op (σ y) X0)) X1))) = X1 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq723905 eq248
    | exact resolve eq248 eq723905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq724481 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq723905 eq223151
    | exact resolve eq223151 eq723905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223151 eq723905
  have eq724625 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (M.op (M.op X0 (M.op (σ x) (σ y))) X1))) = X1 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq450 eq724341
    | exact resolve eq724341 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450 eq724341
  have eq724689 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (σ y) X1))) = X1 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq15317 eq724625
    | exact resolve eq724625 eq15317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15317 eq724625
  have eq755832 : (M.op x x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq724481 eq74
    | exact resolve eq74 eq724481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724481
  have eq756157 : (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq183 eq755832
    | exact resolve eq755832 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq755832
  have eq848925 : (M.op (M.op x y) y) = (M.op (M.op x y) (M.op y (M.op x x))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq756157 eq314978
    | exact resolve eq314978 eq756157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314978 eq756157
  have eq849205 : x = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2522 eq848925
    | exact resolve eq848925 eq2522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2522 eq848925
  have eq1600260 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)))) := by
    first
    | (have i₁ := eq1462
       have i₂ := eq54057 sF0 sF0 sF0 sF0
       grind)
    | exact superpose eq54057 eq1462
    | exact resolve eq1462 eq54057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1462
  have eq1600261 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op x (M.op y (M.op x y)))) := by
    first
    | exact superpose eq2505 eq1600260
    | exact resolve eq1600260 eq2505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2505 eq1600260
  have eq1600262 : (σ (M.op x (M.op y (M.op x y)))) = (M.op (σ (M.op x y)) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq1600261
       have i₂ := eq54057 sF1 sF1 sF1 sF1
       grind)
    | exact superpose eq54057 eq1600261
    | exact resolve eq1600261 eq54057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1600261
  have eq1600263 : (σ (M.op x (M.op y (M.op x y)))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq471763 eq1600262
    | exact resolve eq1600262 eq471763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471763 eq1600262
  have eq1600272 : (σ y) = (σ (M.op x (M.op y (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq724689 eq1600263
    | exact resolve eq1600263 eq724689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724689 eq1600263
  have eq1601099 : (τ (σ y)) = (M.op x (M.op y (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1600272 eq16
    | exact resolve eq16 eq1600272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1600272
  have eq1601226 : y = (M.op x (M.op y (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1601099
    | exact resolve eq1601099 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601099
  have eq1601298 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1601226 eq50
    | exact resolve eq50 eq1601226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1601226
  have eq1602157 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1601298 eq849205
    | exact resolve eq849205 eq1601298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849205 eq1601298
  have eq1602377 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1602157
  have eq1603014 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1602377 eq29
    | exact resolve eq29 eq1602377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1602377
  have eq1603477 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq1603014
    | exact resolve eq1603014 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1603014
  have eq1603478 : x = (M.op x y) ∨ x = y := by grind
  clear eq1603477
  have eq1603612 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1603478 eq20
    | exact resolve eq20 eq1603478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1603683 : ∀ X0 : G, y = (M.op X0 (M.op (M.op X0 x) x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1603478 eq1016
    | exact resolve eq1016 eq1603478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016 eq1603478
  have eq1603995 : y = (M.op y (M.op (M.op x y) x)) ∨ x = y := by
    first
    | (have i₁ := eq1603683 x
       have i₂ := eq91465 x x
       grind)
    | exact superpose eq91465 eq1603683
    | exact resolve eq1603683 eq91465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91465 eq1603683
  have eq1604060 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq1603612
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1603612
    | exact resolve eq1603612 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1603612
  have eq1606561 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (σ (M.op x (M.op (M.op x x) x))) := by
    first
    | (have i₁ := eq1499
       have i₂ := eq54057 x x x x
       grind)
    | exact superpose eq54057 eq1499
    | exact resolve eq1499 eq54057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499
  have eq1606562 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (σ (M.op y (M.op (M.op x y) x))) := by
    first
    | (have i₁ := eq1606561
       have i₂ := eq99874 x x
       grind)
    | exact superpose eq99874 eq1606561
    | exact resolve eq1606561 eq99874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99874 eq1606561
  have eq1606563 : (σ (M.op y (M.op (M.op x y) x))) = (M.op (σ x) (M.op (M.op (σ x) (σ x)) (σ x))) := by
    first
    | (have i₁ := eq1606562
       have i₂ := eq54057 sF2 sF2 sF2 sF2
       grind)
    | exact superpose eq54057 eq1606562
    | exact resolve eq1606562 eq54057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606562
  have eq1606564 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) = (σ (M.op y (M.op (M.op x y) x))) := by
    first
    | exact superpose eq99879 eq1606563
    | exact resolve eq1606563 eq99879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99879 eq1606563
  have eq1633479 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = y := by
    first
    | exact superpose eq1603995 eq1606564
    | exact resolve eq1606564 eq1603995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1603995 eq1606564
  have eq1633943 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq1633479
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1633479
    | exact resolve eq1633479 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1633479
  have eq1683590 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) (M.op X0 (σ y))))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1633943 eq72546
    | exact resolve eq72546 eq1633943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72546 eq1633943
  have eq1683953 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq24497 eq1683590
    | exact resolve eq1683590 eq24497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24497 eq1683590
  have eq1684570 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq1683953 eq27
    | exact resolve eq27 eq1683953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1683953
  have eq1684946 : x = y := by
    first
    | (have r₁ := eq1684570
       have r₂ := eq1604060
       grind)
    | exact resolve eq1684570 eq1604060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604060 eq1684570
  have eq1685077 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1684946
       grind)
    | exact superpose eq1684946 eq18
    | exact resolve eq18 eq1684946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1685078 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1684946
       grind)
    | exact superpose eq1684946 eq24
    | exact resolve eq24 eq1684946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1684946
  have eq1685500 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1685078
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1685078
    | exact resolve eq1685078 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1685078
  have eq1687128 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (σ x)) (M.op (M.op X1 (M.op (σ x) (σ y))) X0)) X2) = (M.op (M.op X0 (σ x)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq1685500 eq4311
    | exact resolve eq4311 eq1685500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4311
  have eq1687129 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ x)) X2) = (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 (M.op X1 (M.op (σ x) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1687128 X2 x X0
       have i₂ := eq676 X0 (M.op x sF4) X2 x sF2
       grind)
    | exact superpose eq676 eq1687128
    | exact resolve eq1687128 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676 eq1687128
  have eq1687130 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ x)) X2) = (M.op X1 (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X1 (M.op (σ x) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1687129 x X1 X2
       have i₂ := eq54057 (M.op X1 (M.op sF2 X2)) X1 sF4 x
       grind)
    | exact superpose eq54057 eq1687129
    | exact resolve eq1687129 eq54057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1687129
  have eq1687131 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ x)) X2) = (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 X1) (M.op (σ x) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1687130 X2 x X2
       have i₂ := eq54057 (M.op sF2 X2) sF4 X2 x
       grind)
    | exact superpose eq54057 eq1687130
    | exact resolve eq1687130 eq54057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54057 eq1687130
  have eq1687132 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ x)) X2) = (M.op X1 (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 X1) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1687131 X0 X1 X2
       have i₂ := eq100962 (M.op X0 X1) sF2 X2 sF4
       grind)
    | (have i₁ := eq1687131 X0 X1 X2
       have i₂ := eq100962 sF4 (M.op X0 X1) X2 sF2
       grind)
    | exact superpose eq100962 eq1687131
    | exact resolve eq1687131 eq100962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100962 eq1687131
  have eq1688544 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) = (M.op X0 (M.op (σ x) (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq72233 eq1687132
    | exact resolve eq1687132 eq72233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72233 eq1687132
  have eq1690377 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq1688544 x
       have i₂ := eq15754 sF2 x sF4
       grind)
    | exact superpose eq15754 eq1688544
    | exact resolve eq1688544 eq15754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15754 eq1688544
  have eq1692272 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq1690377
       have i₂ := eq8139 sF2 sF4 sF3
       grind)
    | (have i₁ := eq1690377
       have i₂ := eq8139 sF4 sF2 sF3
       grind)
    | exact superpose eq8139 eq1690377
    | exact resolve eq1690377 eq8139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8139 eq1690377
  have eq1694066 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2099 eq1692272
    | exact resolve eq1692272 eq2099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2099 eq1692272
  have eq1695727 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1685500 eq1694066
    | exact resolve eq1694066 eq1685500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1685500 eq1694066
  have eq1702714 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1695727 eq74
    | exact resolve eq74 eq1695727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq1695727
  have eq1703243 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1702714
       have i₂ := eq1685077
       grind)
    | exact superpose eq1685077 eq1702714
    | exact resolve eq1702714 eq1685077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1685077 eq1702714
  have eq1703561 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1703243 eq15
    | exact resolve eq15 eq1703243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1703243
  have eq1703645 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1703561
    | exact resolve eq1703561 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1703561
  have eq1703667 : False := by grind
  exact eq1703667

/-- `Equation1590`: `x = (y ◇ z) ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pxy_pxx_pyx_Equation1590 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1590 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1590.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X1 X0)) (M.op (M.op X1 X2) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X1 X2) (M.op X2 (M.op X1 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X0)) = (M.op (M.op (M.op X1 X2) X3) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X1 X0)) (M.op X1 X2) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 (M.op X2 X1)
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op (M.op X2 (M.op X1 X0)) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64 X3 (M.op X2 (M.op X1 X0)) (M.op X1 X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (M.op X0 X1)
       have i₂ := eq64 (M.op (M.op X0 X1) (M.op X1 X2)) X1 X0
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) = (M.op (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    grind
  have eq82 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X0)) = (M.op X1 (M.op (M.op X1 (M.op X2 X3)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq71 X1 (M.op X2 X3) (M.op X3 (M.op X2 X0))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq71
    | exact resolve eq71 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op X3 X0)) = (M.op X1 (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq71 X1 X2 (M.op (M.op X2 X3) (M.op X3 X0))
       have i₂ := eq71 X2 X3 X0
       grind)
    | exact superpose eq71 eq71
    | exact resolve eq71 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X1) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X1 (M.op X0 X1) X2
       have i₂ := eq64 (M.op (M.op X0 X1) X2) X1 X0
       grind)
    | exact superpose eq64 eq71
    | exact resolve eq71 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op X1 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X2 (M.op X1 X0) (M.op (M.op X1 X0) X1)
       have i₂ := eq71 (M.op X1 X0) X1 X0
       grind)
    | exact superpose eq71 eq64
    | exact resolve eq64 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) X3) = (M.op (M.op X0 (M.op X2 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq88 (M.op X1 (M.op X2 X0)) (M.op X2 X1) X3
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq88
    | exact resolve eq88 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X2 X0)) X3) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq88 (M.op (M.op X1 X2) (M.op X2 X0)) X1 X3
       have i₂ := eq71 X1 X2 X0
       grind)
    | exact superpose eq71 eq88
    | exact resolve eq88 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op X1 (M.op (M.op X2 (M.op X3 X1)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 X1 X3 X2 (M.op X2 (M.op X3 X0))
       have i₂ := eq9 X0 X3 X2
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq255 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X1 X0) X4)) = (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X3 X2) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq63 X4 (M.op X1 X0) X3 (M.op X3 X2)
       have i₂ := eq63 X2 X1 X0 X3
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 (M.op X4 X0)))) = (M.op (M.op (M.op X2 X1) (M.op X4 X3)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq63 (M.op X3 (M.op X4 X0)) X2 X1 (M.op X4 X3)
       have i₂ := eq9 X0 X4 X3
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op (M.op X3 X4) (M.op X4 X0)))) = (M.op (M.op (M.op X2 X1) X3) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq63 (M.op (M.op X3 X4) (M.op X4 X0)) X2 X1 X3
       have i₂ := eq71 X3 X4 X0
       grind)
    | exact superpose eq71 eq63
    | exact resolve eq63 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq289 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (M.op X2 (M.op X1 (M.op X0 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq123 X0 X1 X2 X3
       have i₂ := eq258 X3 X2 X1 X0 X2
       grind)
    | exact superpose eq258 eq123
    | exact resolve eq123 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq258
  have eq457 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X1 X0) X3) X4) X5) = (M.op (M.op (M.op X4 (M.op X0 (M.op X1 X2))) (M.op X3 X2)) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq67 (M.op X3 X2) (M.op (M.op X1 X0) X3) X4 X5
       have i₂ := eq63 X2 X1 X0 X3
       grind)
    | exact superpose eq63 eq67
    | exact resolve eq67 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X3 (M.op X0 X3))) X4) = (M.op (M.op (M.op X0 (M.op X1 X2)) X2) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq67 X2 X1 (M.op X3 (M.op X0 X3)) X4
       have i₂ := eq64 (M.op X1 X2) X3 X0
       grind)
    | exact superpose eq64 eq67
    | exact resolve eq67 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq463 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X3 X0) X3)) X4) = (M.op (M.op (M.op X0 (M.op X1 X2)) X2) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq67 X2 X1 (M.op (M.op X3 X0) X3) X4
       have i₂ := eq88 X0 X3 (M.op X1 X2)
       grind)
    | exact superpose eq88 eq67
    | exact resolve eq67 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X2) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X3 X2 (M.op X0 X1) X1
       have i₂ := eq67 X1 X0 X2 (M.op X1 X3)
       grind)
    | exact superpose eq67 eq63
    | exact resolve eq63 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq523 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X3 X0) X3)) X4) = (M.op (M.op X1 X0) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq463 X0 X1 x X3 X4
       have i₂ := eq67 x X1 X0 X4
       grind)
    | exact superpose eq67 eq463
    | exact resolve eq463 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq524 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X1 (M.op X3 (M.op X0 X3))) X4) = (M.op (M.op X1 X0) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq462 X0 X1 x X3 X4
       have i₂ := eq67 x X1 X0 X4
       grind)
    | exact superpose eq67 eq462
    | exact resolve eq462 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq529 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X1 X0) X3) X4) X5) = (M.op (M.op X2 (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2))))) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq457 X0 X1 X2 X3 X4 X5
       have i₂ := eq120 X2 (M.op X4 (M.op X0 (M.op X1 X2))) X3 X5
       grind)
    | (have i₁ := eq457 X0 X1 X2 X3 X4 X5
       have i₂ := eq120 (M.op X4 (M.op X0 (M.op X1 X2))) X2 X3 X5
       grind)
    | exact superpose eq120 eq457
    | exact resolve eq457 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq457
  have eq549 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) = (M.op (M.op X0 X0) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq524 X0 X0 X1 (M.op X1 (M.op X0 X1))
       grind)
    | exact superpose eq524 eq75
    | exact resolve eq75 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq524
  have eq557 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op (M.op X1 X0) X4) X5)) = (M.op (M.op X4 X2) (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq179 X5 (M.op X4 X2) X3 (M.op (M.op X1 X0) X4)
       have i₂ := eq63 X2 X1 X0 X4
       grind)
    | exact superpose eq63 eq179
    | exact resolve eq179 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 X5)) = (M.op (M.op (M.op X0 (M.op X1 X4)) X2) (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq179 X5 (M.op (M.op X0 (M.op X1 X4)) X2) X3 X4
       have i₂ := eq179 X2 X4 X0 X1
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X0 (M.op X1 X2))) = (M.op (M.op X1 X0) (M.op X3 (M.op (M.op X3 X4) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq179 (M.op (M.op X3 X4) X2) X4 (M.op X1 X0) X3
       have i₂ := eq63 X2 X1 X0 (M.op X3 X4)
       grind)
    | exact superpose eq63 eq179
    | exact resolve eq179 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op (M.op X0 X1) X2)) = (M.op (M.op X1 (M.op X0 (M.op X3 X4))) (M.op X3 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq179 X2 X4 (M.op X1 (M.op X0 (M.op X3 X4))) X3
       have i₂ := eq67 (M.op X3 X4) X0 X1 X2
       grind)
    | exact superpose eq67 eq179
    | exact resolve eq179 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X3)) X2) = (M.op (M.op X3 X4) (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op (M.op X0 (M.op X1 X3)) X2) X3 X4
       have i₂ := eq179 X2 X3 X0 X1
       grind)
    | exact superpose eq179 eq9
    | exact resolve eq9 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq600 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) = (M.op (M.op X0 (M.op X1 (M.op X4 X3))) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq85 X4 X3 (M.op (M.op X0 (M.op X1 (M.op X4 X3))) X2)
       have i₂ := eq179 X2 (M.op X4 X3) X0 X1
       grind)
    | exact superpose eq179 eq85
    | exact resolve eq85 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq607 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X1 X0) X3) X4) X5) = (M.op (M.op X0 (M.op X1 X2)) (M.op X4 (M.op X2 (M.op X3 X5)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq529 X0 X1 X2 X3 X4 X5
       have i₂ := eq600 X2 X3 X5 (M.op X0 (M.op X1 X2)) X4
       grind)
    | exact superpose eq600 eq529
    | exact resolve eq529 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq628 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op (M.op X0 X1) X2)) = (M.op (M.op X1 X3) (M.op (M.op X0 (M.op X3 X4)) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq573 X0 X1 X2 X3 X4
       have i₂ := eq474 X1 (M.op X0 (M.op X3 X4)) X3 X2
       grind)
    | (have i₁ := eq573 X0 X1 X2 X3 X4
       have i₂ := eq474 X1 X3 (M.op X0 (M.op X3 X4)) X2
       grind)
    | exact superpose eq474 eq573
    | exact resolve eq573 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq636 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 X5)) = (M.op (M.op (M.op X0 (M.op X1 X4)) X2) (M.op X2 (M.op X1 (M.op X3 (M.op X0 X5))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq561 X0 X1 X2 X3 X4 X5
       have i₂ := eq600 X3 X0 X5 X2 X1
       grind)
    | exact superpose eq600 eq561
    | exact resolve eq561 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq640 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op (M.op X1 X0) X4) X5)) = (M.op (M.op X4 X2) (M.op X2 (M.op X1 (M.op X3 (M.op X0 X5))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq557 X0 X1 X2 X3 X4 X5
       have i₂ := eq600 X3 X0 X5 X2 X1
       grind)
    | exact superpose eq600 eq557
    | exact resolve eq557 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557 eq600
  have eq654 : ∀ X0 X1 X3 X4 X5 : G, (M.op X3 (M.op X4 X5)) = (M.op (M.op X1 (M.op X3 (M.op X0 (M.op X1 X4)))) (M.op X0 X5)) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq636 X0 X1 x X3 X4 X5
       have i₂ := eq588 X1 X3 (M.op X0 X5) (M.op X0 (M.op X1 X4)) x
       grind)
    | exact superpose eq588 eq636
    | exact resolve eq636 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq655 : ∀ X0 X1 X3 X4 X5 : G, (M.op X3 (M.op (M.op (M.op X1 X0) X4) X5)) = (M.op (M.op X1 (M.op X3 X4)) (M.op X0 X5)) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq640 X0 X1 x X3 X4 X5
       have i₂ := eq588 X1 X3 (M.op X0 X5) X4 x
       grind)
    | exact superpose eq588 eq640
    | exact resolve eq640 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588 eq640
  have eq662 : ∀ X0 X1 X3 X4 X5 : G, (M.op X3 (M.op X4 X5)) = (M.op (M.op X1 X0) (M.op (M.op X3 (M.op X0 (M.op X1 X4))) X5)) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq654 X0 X1 X3 X4 X5
       have i₂ := eq474 X1 (M.op X3 (M.op X0 (M.op X1 X4))) X0 X5
       grind)
    | (have i₁ := eq654 X0 X1 X3 X4 X5
       have i₂ := eq474 X1 X0 (M.op X3 (M.op X0 (M.op X1 X4))) X5
       grind)
    | exact superpose eq474 eq654
    | exact resolve eq654 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474 eq654
  have eq664 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X1 X0) X3) X4) X5) = (M.op X1 (M.op (M.op (M.op X0 X4) X2) (M.op X2 (M.op X3 X5)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq607 X0 X1 X2 X3 X4 X5
       have i₂ := eq655 X4 X0 X1 X2 (M.op X2 (M.op X3 X5))
       grind)
    | exact superpose eq655 eq607
    | exact resolve eq607 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq668 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X1 X0) X4)) = (M.op X1 (M.op (M.op (M.op X0 (M.op X3 X2)) X2) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq255 X0 X1 X2 X3 X4
       have i₂ := eq655 (M.op X3 X2) X0 X1 X2 X4
       grind)
    | exact superpose eq655 eq255
    | exact resolve eq255 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq655
  have eq671 : ∀ X1 X3 X4 X5 : G, (M.op X3 (M.op X4 X5)) = (M.op (M.op X1 X4) (M.op (M.op X3 X1) X5)) := by
    intro X1 X3 X4 X5
    first
    | (have i₁ := eq662 x X1 X3 X4 X5
       have i₂ := eq628 X3 X1 X5 x (M.op X1 X4)
       grind)
    | exact superpose eq628 eq662
    | exact resolve eq662 eq628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628 eq662
  have eq672 : ∀ X0 X1 X3 X4 : G, (M.op X3 (M.op (M.op X1 X0) X4)) = (M.op X1 (M.op (M.op X3 X0) X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq668 X0 X1 x X3 X4
       have i₂ := eq67 x X3 X0 X4
       grind)
    | exact superpose eq67 eq668
    | exact resolve eq668 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq676 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X1 X0) X3) X4) X5) = (M.op X1 (M.op X4 (M.op X0 (M.op X3 X5)))) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq664 X0 X1 x X3 X4 X5
       have i₂ := eq63 (M.op X3 X5) X0 X4 x
       grind)
    | exact superpose eq63 eq664
    | exact resolve eq664 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq798 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op (M.op (M.op (M.op X1 (M.op X2 X3)) X3) X4) X5)) = (M.op (M.op X2 X1) (M.op (M.op X0 X4) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq67 X3 X2 X1 (M.op (M.op X0 X4) X5)
       have i₂ := eq672 X4 X0 (M.op (M.op X1 (M.op X2 X3)) X3) X5
       grind)
    | (have i₁ := eq67 X3 X2 X1 (M.op (M.op X0 X4) X5)
       have i₂ := eq672 X4 (M.op (M.op X1 (M.op X2 X3)) X3) X0 X5
       grind)
    | exact superpose eq672 eq67
    | exact resolve eq67 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq672
  have eq799 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X2 X1) (M.op (M.op X0 X4) X5)) = (M.op X0 (M.op X1 (M.op X4 (M.op (M.op X2 X3) (M.op X3 X5))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq798 X0 X1 X2 X3 X4 X5
       have i₂ := eq676 (M.op X2 X3) X1 X3 X4 X5
       grind)
    | exact superpose eq676 eq798
    | exact resolve eq798 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676 eq798
  have eq888 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X2 X1) (M.op (M.op X0 X4) X5)) = (M.op X0 (M.op (M.op (M.op X4 X1) X2) X5)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq799 X0 X1 X2 x X4 X5
       have i₂ := eq262 X5 X1 X4 X2 x
       grind)
    | exact superpose eq262 eq799
    | exact resolve eq799 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262 eq799
  have eq1287 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X4) (M.op X0 (M.op X1 X2))) = (M.op X5 (M.op (M.op X5 X3) (M.op (M.op X4 (M.op X1 X0)) X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq84 (M.op (M.op X4 (M.op X1 X0)) X2) X5 X3 X4
       have i₂ := eq82 X2 X4 X1 X0
       grind)
    | exact superpose eq82 eq84
    | exact resolve eq84 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq1357 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X5 X2))) = (M.op (M.op (M.op X4 X3) (M.op X1 X5)) (M.op X0 (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq63 (M.op X5 X2) X4 X3 (M.op X1 X5)
       have i₂ := eq84 X2 X0 X1 X5
       grind)
    | exact superpose eq84 eq63
    | exact resolve eq63 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq84
  have eq1442 : ∀ X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X5 X2))) = (M.op X1 (M.op (M.op X1 X5) (M.op (M.op X4 X3) X2))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1357 x X1 X2 X3 X4 X5
       have i₂ := eq572 (M.op X1 X5) (M.op X4 X3) X2 x X1
       grind)
    | exact superpose eq572 eq1357
    | exact resolve eq1357 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq1357
  have eq1538 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) (M.op X0 (M.op X1 X2))) = (M.op (M.op X1 X0) (M.op X4 (M.op X3 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1287 X0 X1 X2 X3 X4 x
       have i₂ := eq1442 x X2 (M.op X1 X0) X4 X3
       grind)
    | exact superpose eq1442 eq1287
    | exact resolve eq1287 eq1442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287 eq1442
  have eq2842 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2907 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op X0 X1) X0) X2) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq88 X0 X0 X2
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq88 X1 X0 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq88
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq88 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2970 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2842 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2842
  have eq2971 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2970 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2970
  have eq2989 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 X2) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2907 X0 X1 X2
       have i₂ := eq88 X1 X0 X2
       grind)
    | exact superpose eq88 eq2907
    | (have j0 := eq2907 X0 X1 X2
       grind)
    | exact resolve eq2907 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2907
  have eq8075 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2971 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2971
  have eq8083 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq8075 X0 X1
       have j1 := eq2989 X0 X1 x
       grind)
    | (have r₁ := eq8075 X0 X1
       have r₂ := eq2989 X0 X1 X0
       grind)
    | (have r₁ := eq8075 X1 X0
       have r₂ := eq2989 X0 X1 X1
       grind)
    | (have r₁ := eq8075 X1 X1
       have r₂ := eq2989 (M.op X1 X1) X1 x
       grind)
    | exact resolve eq8075 eq2989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2989 eq8075
  have eq8265 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq8452 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq8265 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8265
  have eq8520 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq8452 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8452
  have eq8610 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq8520 (σ X0)
       grind)
    | exact superpose eq8520 eq15
    | exact resolve eq15 eq8520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8629 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8610 X0
       have i₂ := eq8520 X0
       grind)
    | exact superpose eq8520 eq8610
    | exact resolve eq8610 eq8520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8520 eq8610
  have eq8889 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq85 (σ X0) (σ X0) X1
       have i₂ := eq8629 X0
       grind)
    | exact superpose eq8629 eq85
    | exact resolve eq85 eq8629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq8890 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (M.op (σ (M.op X0 X0)) (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq88 (σ X0) (σ X0) X1
       have i₂ := eq8629 X0
       grind)
    | exact superpose eq8629 eq88
    | exact resolve eq88 eq8629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq8920 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq8925 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8083 X1 (σ X0)
       have i₂ := eq8629 X0
       grind)
    | exact superpose eq8629 eq8083
    | (have j0 := eq8083 X1 (σ X0)
       grind)
    | exact resolve eq8083 eq8629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8929 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq8920 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq8920
    | exact resolve eq8920 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8920
  have eq8934 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq8929
  have eq8935 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op (M.op X0 X0) X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8890 X0 X1
       have i₂ := eq8934 X0
       grind)
    | exact superpose eq8934 eq8890
    | exact resolve eq8890 eq8934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8890 eq8934
  have eq9302 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X0 X1) X0)) X2) = (M.op (σ (M.op (M.op (M.op (M.op X0 X1) X0) X1) (M.op (M.op X0 X1) X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8935 (M.op (M.op X0 X1) X0) X2
       have i₂ := eq523 X1 (M.op (M.op X0 X1) X0) X0 (M.op (M.op X0 X1) X0)
       grind)
    | exact superpose eq523 eq8935
    | exact resolve eq8935 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq9486 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X0 X1) X0)) X2) = (M.op (σ (M.op X0 (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X1) X0)) X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9302 X0 X1 X2
       have i₂ := eq888 X0 X1 (M.op (M.op X0 X1) X0) X1 X0
       grind)
    | exact superpose eq888 eq9302
    | exact resolve eq9302 eq888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888 eq9302
  have eq9533 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X0 X1) X0)) X2) = (M.op (σ (M.op (M.op X1 X1) (M.op (M.op X0 X1) X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9486 X0 X1 X2
       have i₂ := eq179 X0 X0 (M.op X1 X1) (M.op X0 X1)
       grind)
    | exact superpose eq179 eq9486
    | exact resolve eq9486 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq9486
  have eq9562 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X0 X1) X0)) X2) = (M.op (σ (M.op X0 (M.op X1 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9533 X0 X1 X2
       have i₂ := eq671 X1 X0 X1 X0
       grind)
    | (have i₁ := eq9533 x X1 X2
       have i₂ := eq671 X1 (M.op X1 X1) (M.op x X1) x
       grind)
    | exact superpose eq671 eq9533
    | exact resolve eq9533 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9533
  have eq9583 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8935 X0 X1
       have i₂ := eq9562 X0 X0 X1
       grind)
    | exact superpose eq9562 eq8935
    | exact resolve eq8935 eq9562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8935 eq9562
  have eq9991 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) = (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq8629 (M.op X0 (M.op X0 X0))
       have i₂ := eq9583 X0 (σ (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq9583 eq8629
    | exact resolve eq8629 eq9583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10047 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (σ X0) (M.op X1 (M.op X2 X3)))) = (M.op (M.op X1 (σ (M.op X0 (M.op X0 X0)))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq289 X1 (σ (M.op X0 (M.op X0 X0))) X2 X3
       have i₂ := eq9583 X0 (M.op X1 (M.op X2 X3))
       grind)
    | exact superpose eq9583 eq289
    | exact resolve eq289 eq9583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10064 : ∀ X0 : G, (k (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) (σ (M.op X0 (M.op X0 X0)))) = (M.op (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    grind
  clear eq9583
  have eq10090 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (σ X0)) X3) = (M.op (M.op X1 (σ (M.op X0 (M.op X0 X0)))) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq10047 X0 X1 x X3
       have i₂ := eq289 X1 (σ X0) x X3
       grind)
    | exact superpose eq289 eq10047
    | exact resolve eq10047 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq10047
  have eq10131 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9991 X0
       have i₂ := eq1538 X0 X0 X0 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq9991 X0
       have i₂ := eq1538 (M.op X0 X0) X0 X0 X0 X0
       grind)
    | exact superpose eq1538 eq9991
    | exact resolve eq9991 eq1538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538 eq9991
  have eq10186 : ∀ X0 : G, (k (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) (σ (M.op X0 (M.op X0 X0)))) = (M.op (M.op (σ X0) (σ X0)) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq10064 X0
       have i₂ := eq10090 X0 (σ X0) (σ (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq10090 eq10064
    | exact resolve eq10064 eq10090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10064 eq10090
  have eq10204 : ∀ X0 : G, (σ (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq10131 X0
       have i₂ := eq671 X0 X0 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq10131 X0
       have i₂ := eq671 x (M.op X0 X0) (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq671 eq10131
    | exact resolve eq10131 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671 eq10131
  have eq10227 : ∀ X0 : G, (k (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) (σ (M.op X0 (M.op X0 X0)))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq10186 X0
       have i₂ := eq8629 X0
       grind)
    | exact superpose eq8629 eq10186
    | exact resolve eq10186 eq8629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10186
  have eq10252 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 (M.op X0 X0)))) = (k (σ (M.op X0 (M.op X0 (M.op X0 X0)))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq10227 X0
       have i₂ := eq10204 X0
       grind)
    | exact superpose eq10204 eq10227
    | exact resolve eq10227 eq10204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10204 eq10227
  have eq10266 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 (M.op X0 X0)))) = (σ (k (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq10252 X0
       have i₂ := eq15 (M.op X0 (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq15 eq10252
    | exact resolve eq10252 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10252
  have eq10271 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 (M.op X0 X0)))) = (σ (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq10266 X0
       have i₂ := eq549 X0 X0
       grind)
    | exact superpose eq549 eq10266
    | exact resolve eq10266 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549 eq10266
  have eq10275 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq10271 X0
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq10271
    | exact resolve eq10271 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10271
  have eq16087 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq8889 X0 (σ (M.op X0 (M.op X0 X0)))
       have i₂ := eq10275 X0
       grind)
    | exact superpose eq10275 eq8889
    | exact resolve eq8889 eq10275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8889 eq10275
  have eq16162 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq16087 X0
       have i₂ := eq8629 X0
       grind)
    | exact superpose eq8629 eq16087
    | exact resolve eq16087 eq8629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8629 eq16087
  have eq22643 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq8925 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq8925 X0 (σ X0)
       grind)
    | exact superpose eq8925 eq10
    | (have j1 := eq8925 X1 X0
       grind)
    | exact resolve eq10 eq8925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8925
  have eq28025 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq22643 (σ X1) X0
       grind)
    | exact superpose eq22643 eq15
    | (have j1 := eq22643 (σ X1) X0
       grind)
    | exact resolve eq15 eq22643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22643
  have eq28040 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28025 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq28025
    | (have j0 := eq28025 X0 X1
       grind)
    | exact resolve eq28025 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28025
  have eq29541 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28040 X0 X1
       have i₂ := eq8083 X1 X0
       grind)
    | exact superpose eq8083 eq28040
    | (have j0 := eq28040 X0 X1
       have j1 := eq8083 X1 X0
       grind)
    | exact resolve eq28040 eq8083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8083 eq28040
  have eq29753 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq29541 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29541
  have eq31080 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16162 X0
       have i₂ := eq29753 X0 X1
       grind)
    | (have i₁ := eq16162 X0
       have i₂ := eq29753 X0 (M.op X0 X0)
       grind)
    | exact superpose eq29753 eq16162
    | (have j1 := eq29753 X1 X0
       grind)
    | exact resolve eq16162 eq29753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16162 eq29753
  have eq31219 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq31080 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31080
  have eq31695 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31219 y x
       grind)
    | exact superpose eq31219 eq16
    | (have r₁ := eq16
       have r₂ := eq31219 y x
       grind)
    | exact resolve eq16 eq31219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31219
  have eq31697 : False := by grind
  exact eq31697

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pxx_pxx_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (M.op X1 X2) X2) X3) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op (M.op X1 X2) X2) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq84 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X2) X2) x
       have i₂ := eq20 (M.op X0 (M.op (M.op X1 X2) X2)) X1 X2 x
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq114 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X1 X1) = (k X1 (M.op X0 (M.op (M.op X1 X2) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (M.op X0 (M.op (M.op X1 X2) X2))
       have i₂ := eq95 X0 X1 X2
       grind)
    | exact superpose eq95 eq12
    | (have j0 := eq12 X1 (M.op X0 (M.op (M.op X1 X2) X2))
       grind)
    | (have r₁ := eq12 X0 (M.op X0 (M.op (M.op X0 X2) X2))
       have r₂ := eq95 X0 X0 X2
       grind)
    | exact resolve eq12 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 (M.op (M.op X2 X3) X3))) (M.op X0 X2)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op (M.op X2 X3) X3)) X2
       have i₂ := eq95 X0 X2 X3
       grind)
    | exact superpose eq95 eq9
    | exact resolve eq9 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X2)) = (M.op X0 (M.op (M.op X1 X3) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 (M.op (M.op X1 X3) X3)) X1 X2
       have i₂ := eq95 X0 X1 X3
       grind)
    | exact superpose eq95 eq9
    | exact resolve eq9 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq56 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq56
    | exact resolve eq56 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq169 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq158 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq158
    | (have j0 := eq158 X0
       grind)
    | exact resolve eq158 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq158
  have eq170 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq169 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq169
    | (have j0 := eq169 X0
       grind)
    | exact resolve eq169 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq171 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq170 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq170 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq170 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq174 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq171 (σ X0)
       grind)
    | exact superpose eq171 eq15
    | exact resolve eq15 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq171 X0
       grind)
    | exact superpose eq171 eq174
    | exact resolve eq174 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq174
  have eq201 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (M.op (σ X0) X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq185 X0
       grind)
    | exact superpose eq185 eq9
    | exact resolve eq9 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq16
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ (k X0 X1)) (M.op (M.op (σ X0) X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) (σ X0) X2
       have i₂ := eq79 X1 X0
       grind)
    | exact superpose eq79 eq9
    | (have j1 := eq79 X0 X1
       grind)
    | exact resolve eq9 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq1105 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X0 (M.op (M.op X2 X3) X3)) (M.op (M.op X2 X4) X4))) X0) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq115 (M.op X0 (M.op (M.op X2 X3) X3)) X1 X2 X4
       have i₂ := eq95 X0 X2 X3
       grind)
    | exact superpose eq95 eq115
    | exact resolve eq115 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq115
  have eq1617 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq1663 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1617 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1617
    | (have j0 := eq1617 X0 X1
       grind)
    | exact resolve eq1617 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1617
  have eq1725 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op (M.op X0 X1) X1))) := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq1770 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X3) X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1725 X0 (M.op (M.op X1 X2) X2)
       have i₂ := eq116 (M.op X0 (M.op (M.op X1 X2) X2)) X1 X2 X3
       grind)
    | (have i₁ := eq1725 X0 (M.op (M.op X1 X2) X2)
       have i₂ := eq116 (M.op X0 (M.op (M.op X1 X2) X2)) X1 X3 X2
       grind)
    | exact superpose eq116 eq1725
    | exact resolve eq1725 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq1725
  have eq2654 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq216
       have i₂ := eq1663 x y
       grind)
    | exact superpose eq1663 eq216
    | (have j1 := eq1663 (σ x) (σ y)
       grind)
    | (have r₁ := eq216
       have r₂ := eq1663 x y
       grind)
    | (have r₁ := eq216
       have r₂ := eq1663 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq216
       have r₂ := eq1663 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq216 eq1663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq1663
  have eq2655 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq2654
  have eq5949 : ∀ X0 X1 X2 : G, (M.op (σ X1) X0) = X0 ∨ (σ X1) = X0 ∨ (σ X1) = (M.op (σ (k (τ X0) X1)) (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq217 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq217
    | exact resolve eq217 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5966 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ (k y x)) (M.op (M.op (σ y) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq217 y x X0
       grind)
    | exact superpose eq217 eq16
    | (have j1 := eq217 x y x
       grind)
    | exact resolve eq16 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq6025 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (k X0 (σ X1)) (M.op (M.op X0 X2) X2)) ∨ (M.op (σ X1) X0) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5949 X0 X1 X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq5949
    | (have j0 := eq5949 X0 X1 X2
       grind)
    | exact resolve eq5949 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5949
  have eq24305 : ∀ X0 X1 X2 : G, (M.op (k X1 X0) (M.op (M.op X1 X2) X2)) = X0 ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6025 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6025
    | exact resolve eq6025 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6025
  have eq30196 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2655
       grind)
    | exact superpose eq2655 eq16
    | exact resolve eq16 eq2655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2655
  have eq30197 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq30196
       have r₂ := eq185 x
       grind)
    | exact resolve eq30196 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30196
  have eq30440 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq30197
       grind)
    | exact superpose eq30197 eq9
    | exact resolve eq9 eq30197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30197
  have eq89663 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq30440 X0
       grind)
    | exact superpose eq30440 eq12
    | (have j0 := eq12 (σ y) (σ x)
       have j1 := eq30440 X0
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq30440 X0
       grind)
    | exact resolve eq12 eq30440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30440
  have eq89731 : ∀ X0 : G, (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have j0 := eq89663 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89663
  have eq89786 : ∀ X0 : G, (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq89731 X0
       have i₂ := eq185 y
       grind)
    | exact superpose eq185 eq89731
    | (have j0 := eq89731 X0
       grind)
    | exact resolve eq89731 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89731
  have eq89815 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ x = (M.op y (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq89786 X0
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq89786
    | (have j0 := eq89786 X0
       grind)
    | exact resolve eq89786 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89786
  have eq212684 : ∀ X0 : G, y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ x = (M.op y (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq89815 X0
       grind)
    | exact superpose eq89815 eq10
    | (have j1 := eq89815 X0
       grind)
    | exact resolve eq10 eq89815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89815
  have eq212892 : ∀ X0 : G, x = y ∨ (σ (k y x)) = (σ (M.op y y)) ∨ x = (M.op y (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq212684 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq212684
    | (have j0 := eq212684 X0
       grind)
    | exact resolve eq212684 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212684
  have eq212903 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ x = (M.op y (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq212892 X0
       grind)
    | exact superpose eq212892 eq16
    | (have j1 := eq212892 X0
       grind)
    | exact resolve eq16 eq212892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212892
  have eq212904 : ∀ X0 : G, (σ (k y x)) = (σ (M.op y y)) ∨ x = (M.op y (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have j0 := eq212903 X0
       grind)
    | (have r₁ := eq212903 X0
       have r₂ := eq185 x
       grind)
    | exact resolve eq212903 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212903
  have eq213736 : ∀ X0 : G, (k y x) = (τ (σ (M.op y y))) ∨ x = (M.op y (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq212904 X0
       grind)
    | exact superpose eq212904 eq10
    | (have j1 := eq212904 X0
       grind)
    | exact resolve eq10 eq212904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212904
  have eq213946 : ∀ X0 : G, (k y x) = (M.op y y) ∨ x = (M.op y (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq213736 X0
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq213736
    | (have j0 := eq213736 X0
       grind)
    | exact resolve eq213736 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213736
  have eq213986 : ∀ X0 X1 : G, x = (M.op (M.op y y) (M.op (M.op y X0) X0)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op y (M.op (M.op y X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24305 x y X0
       have i₂ := eq213946 X1
       grind)
    | exact superpose eq213946 eq24305
    | (have j0 := eq24305 x y x
       have j1 := eq213946 X1
       grind)
    | exact resolve eq24305 eq213946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24305 eq213946
  have eq214029 : ∀ X1 : G, x = y ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op y (M.op (M.op y X1) X1)) := by
    intro X1
    first
    | (have i₁ := eq213986 x X1
       have i₂ := eq9 y y x
       grind)
    | exact superpose eq9 eq213986
    | (have j0 := eq213986 x X1
       grind)
    | exact resolve eq213986 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213986
  have eq214030 : ∀ X1 : G, x = y ∨ y = (M.op x y) ∨ x = (M.op y (M.op (M.op y X1) X1)) := by
    intro X1
    first
    | (have j0 := eq214029 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214029
  have eq214824 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq214030 x
       grind)
    | exact superpose eq214030 eq16
    | (have j1 := eq214030 X0
       grind)
    | exact resolve eq16 eq214030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214030
  have eq214827 : ∀ X0 : G, y = (M.op x y) ∨ x = (M.op y (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have j0 := eq214824 X0
       grind)
    | (have r₁ := eq214824 X0
       have r₂ := eq185 x
       grind)
    | exact resolve eq214824 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214824
  have eq214837 : ∀ X0 X1 : G, x = (M.op y (M.op (M.op y X0) X0)) ∨ x = (M.op y (M.op (M.op y X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq214827 X1
       grind)
    | exact superpose eq214827 eq9
    | (have j1 := eq214827 X0
       grind)
    | exact resolve eq9 eq214827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214827
  have eq216619 : ∀ X0 : G, x ≠ x ∨ x = (M.op y (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have j0 := eq214837 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214837
  have eq216620 : ∀ X0 : G, x = (M.op y (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have j0 := eq216619 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216619
  have eq216784 : (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq1770 y x x x
       have i₂ := eq216620 (M.op (M.op x x) x)
       grind)
    | exact superpose eq216620 eq1770
    | exact resolve eq1770 eq216620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1770
  have eq216833 : y = (M.op x y) := by
    first
    | (have i₁ := eq1105 y y x x x
       have i₂ := eq216620 (M.op (M.op x x) x)
       grind)
    | exact superpose eq216620 eq1105
    | exact resolve eq1105 eq216620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105 eq216620
  have eq218486 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ (k y x)) (M.op (M.op (σ y) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5966 X0
       have i₂ := eq216833
       grind)
    | exact superpose eq216833 eq5966
    | (have j0 := eq5966 X0
       grind)
    | exact resolve eq5966 eq216833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5966 eq216833
  have eq218611 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ x) = (M.op (σ (k y x)) (M.op (M.op (σ y) X0) X0)) := by
    intro X0
    first
    | (have j0 := eq218486 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218486
  have eq218645 : ∀ X0 : G, (σ x) = (M.op (σ (M.op y y)) (M.op (M.op (σ y) X0) X0)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq218611 X0
       have i₂ := eq216784
       grind)
    | exact superpose eq216784 eq218611
    | exact resolve eq218611 eq216784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216784 eq218611
  have eq218647 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq218645 x
       have i₂ := eq201 y x
       grind)
    | exact superpose eq201 eq218645
    | exact resolve eq218645 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq218645
  have eq218648 : (σ x) = (σ y) := by grind
  clear eq218647
  have eq218652 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq218648
       grind)
    | exact superpose eq218648 eq10
    | exact resolve eq10 eq218648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218648
  have eq218868 : x = y := by
    first
    | (have i₁ := eq218652
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq218652
    | exact resolve eq218652 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218652
  have eq219950 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq218868
       grind)
    | exact superpose eq218868 eq16
    | exact resolve eq16 eq218868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218868
  have eq219959 : False := by grind
  exact eq219959

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_pxy_pyy_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq24 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq24 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq24 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
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
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq39 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq39 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq44 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq44 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq46 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq25 X1
       grind)
    | exact superpose eq25 eq49
    | (have j0 := eq49 X0 X1
       grind)
    | exact resolve eq49 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 X1
       have i₂ := eq25 X1
       grind)
    | exact superpose eq25 eq50
    | (have j0 := eq50 X0 X1
       grind)
    | exact resolve eq50 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq50
  have eq58 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       have j1 := eq55 X0 X1
       grind)
    | (have r₁ := eq56 X0 X1
       have r₂ := eq55 X0 X1
       grind)
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq56
  have eq102 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq106 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       have j1 := eq58 X0 X1
       grind)
    | (have r₁ := eq102 X0 X1
       have r₂ := eq58 X0 X1
       grind)
    | (have r₁ := eq102 X0 X0
       have r₂ := eq58 X0 X0
       grind)
    | exact resolve eq102 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq102
  have eq267 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq106 (σ X0) (σ X1)
       grind)
    | exact superpose eq106 eq15
    | exact resolve eq15 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq267 X0 X1
       have i₂ := eq106 X0 X1
       grind)
    | exact superpose eq106 eq267
    | exact resolve eq267 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq267
  have eq274 : False := by grind
  exact eq274

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq24 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq24 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq24 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq48 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq44 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq46 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq47 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq47 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq47 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq48 X1 X0
       grind)
    | (have r₁ := eq53 X1 X0
       have r₂ := eq48 X0 X1
       grind)
    | exact resolve eq53 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq53
  have eq59 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq25 X1
       grind)
    | exact superpose eq25 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq57
  have eq109 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq113 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq109 X0 X1
       have j1 := eq59 X0 X1
       grind)
    | (have r₁ := eq109 X0 X1
       have r₂ := eq59 X0 X1
       grind)
    | (have r₁ := eq109 X1 X1
       have r₂ := eq59 X1 X1
       grind)
    | exact resolve eq109 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq109
  have eq267 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq113 (σ X0) (σ X1)
       grind)
    | exact superpose eq113 eq15
    | exact resolve eq15 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq267 X0 X1
       have i₂ := eq113 X0 X1
       grind)
    | exact superpose eq113 eq267
    | exact resolve eq267 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq267
  have eq277 : False := by grind
  exact eq277

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_x_pyy_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq51 : x ≠ (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) := by
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
  have eq60 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
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
  have eq61 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ X0 ∨ (M.op (M.op X0 X2) X0) = (k (M.op (M.op X0 X2) X0) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 X2) X0) (M.op X1 X1)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X0 X2) X0) (M.op X1 X1)
       grind)
    | (have r₁ := eq13 (M.op (M.op (M.op X1 X1) X2) (M.op X1 X1)) (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
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
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq21 eq80
    | exact resolve eq80 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq88 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq23
  have eq89 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq90 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq103 : ∀ X0 X1 X2 : G, (M.op (k X0 (M.op X0 X0)) (M.op (M.op X1 X2) X1)) = X1 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0 X1 X2
    grind
  have eq104 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq89
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq104
  have eq129 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
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
  have eq212 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 X0) x) := by
    intro X0
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq60 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq60 X1 X3 x
       have i₂ := eq60 X1 X0 x
       grind)
    | (have i₁ := eq60 X0 X1 X0
       have i₂ := eq60 X0 X0 x
       grind)
    | exact superpose eq60 eq60
    | exact resolve eq60 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 X0 x X2
       have i₂ := eq60 X0 x X1
       grind)
    | (have i₁ := eq60 X2 X2 X2
       have i₂ := eq60 X2 X1 X2
       grind)
    | exact superpose eq60 eq60
    | exact resolve eq60 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 (M.op (M.op X0 X1) X0) x X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) x) X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq57 eq60
    | exact resolve eq60 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq380 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 x
       have i₂ := eq60 X1 X0 x
       grind)
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq60 X0 X0 X2
       grind)
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (k X0 (M.op X0 X0))) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0 X1
    grind
  have eq496 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) = (k (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq61 (M.op X0 X0) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq581 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (k X1 (M.op X1 X1))) = (M.op X0 (k X1 (M.op X1 X1))) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq60 (k X1 (M.op X1 X1)) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq103 X1 X0 x
       grind)
    | exact superpose eq103 eq60
    | (have j1 := eq103 X1 X1 x
       grind)
    | exact resolve eq60 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq706 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X2 X2) (M.op (σ (k X0 X1)) (σ X0))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) X2 (σ X1)
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq14
    | (have j1 := eq68 X0 X1
       grind)
    | exact resolve eq14 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : ∀ X0 : G, (σ x) = (M.op (σ (k X0 X0)) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq58 (σ X0)
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq58
    | (have j1 := eq68 X0 X0
       grind)
    | exact resolve eq58 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq713 : ∀ X0 X1 X2 : G, (σ (k X0 X0)) = (M.op (M.op X1 X1) (M.op X2 (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 X0 X1 (σ X1)
       have i₂ := eq68 X1 X1
       grind)
    | exact superpose eq68 eq59
    | (have j1 := eq68 X0 X0
       grind)
    | exact resolve eq59 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq68 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq721 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq720 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq728 : ∀ X0 X1 X2 : G, (σ (k X0 X0)) = (M.op (M.op X1 X1) (M.op X2 (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq713 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq730 : ∀ X0 : G, (σ x) = (M.op (σ (k X0 X0)) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq711 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq987 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq375 sF0
       have i₂ := eq373 sF0 x x
       grind)
    | (have i₁ := eq375 sF0
       have i₂ := eq373 sF0 x x
       grind)
    | exact superpose eq373 eq375
    | exact resolve eq375 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1007 : ∀ X0 X1 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op (M.op X1 X1) (M.op (M.op (M.op x y) x) X0)) := by
    intro X0 X1
    first
    | exact superpose eq375 eq60
    | exact resolve eq60 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq1160 : ∀ X0 X1 : G, (M.op x (M.op (M.op (M.op x y) X0) (M.op x y))) = (M.op (M.op X1 X1) (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq987 eq60
    | exact resolve eq60 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq1163 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op (M.op x y) X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1160 x x
       have i₂ := eq14 sF0 x x
       grind)
    | exact superpose eq14 eq1160
    | exact resolve eq1160 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160
  have eq1187 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq359 X3 X1 x
       have i₂ := eq359 X0 X1 x
       grind)
    | (have i₁ := eq359 X0 X1 X3
       have i₂ := eq359 (M.op X3 X3) X1 X3
       grind)
    | exact superpose eq359 eq359
    | exact resolve eq359 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1199 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X1))) = (M.op (M.op X2 X2) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq359 X0 (M.op X1 X1) X3
       have i₂ := eq359 X0 X1 X1
       grind)
    | (have i₁ := eq359 X0 (M.op X1 X1) X3
       have i₂ := eq359 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq359 eq359
    | exact resolve eq359 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1235 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X2 X3) X2)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) X3
       have i₂ := eq359 X0 X1 X1
       grind)
    | (have i₁ := eq14 X0 (M.op X1 X1) X2
       have i₂ := eq359 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq359 eq14
    | exact resolve eq14 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1241 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq60 X2 (M.op X1 X1) X3
       have i₂ := eq359 X0 X1 X1
       grind)
    | (have i₁ := eq60 X0 (M.op X1 X1) X2
       have i₂ := eq359 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq359 eq60
    | exact resolve eq60 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq1246 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op X1 X1)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq212 (M.op X1 X1)
       have i₂ := eq359 X0 X1 X1
       grind)
    | (have i₁ := eq212 (M.op X1 X1)
       have i₂ := eq359 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq359 eq212
    | exact resolve eq212 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq1248 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) X2) = (M.op (M.op X3 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq371 (M.op X1 X1) X2 X3
       have i₂ := eq359 X0 X1 X1
       grind)
    | (have i₁ := eq371 (M.op X1 X1) X1 X3
       have i₂ := eq359 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq359 eq371
    | exact resolve eq371 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq1294 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1199 X0 X1 x X3
       have i₂ := eq59 X0 x X1
       grind)
    | exact superpose eq59 eq1199
    | exact resolve eq1199 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq1199
  have eq1553 : ∀ X0 X1 : G, (M.op x y) = (M.op x (M.op (M.op X0 (M.op X1 X1)) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1163 (M.op X1 X1)
       have i₂ := eq1187 sF0 X1 x
       grind)
    | (have i₁ := eq1163 (M.op X1 X1)
       have i₂ := eq1187 X0 X1 sF0
       grind)
    | exact superpose eq1187 eq1163
    | exact resolve eq1163 eq1187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq3048 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) X3) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2)) = X2 := by
    intro X0 X1 X2 X3
    by_contra hcon
    push Not at hcon
    have f3048_12 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
      intro X0 X1 X2
      grind
    have f3048_18 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
      intro X0 X1 X2
      grind
    have f3048_20 : X2 ≠ (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) X3) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2)) := by grind
    have f3048_23 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
      intro X0 X1 X2
      first
      | (have i₁ := f3048_18 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
         have i₂ := f3048_18 X0 (M.op (M.op X0 X2) X0) X2
         grind)
      | exact superpose f3048_18 f3048_18
      | exact resolve f3048_18 f3048_18
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f3048_27 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
      intro X0 X1 X3
      first
      | (have i₁ := f3048_12 X3 X1 x
         have i₂ := f3048_12 X0 X1 x
         grind)
      | (have i₁ := f3048_12 X0 X1 x
         have i₂ := f3048_12 (M.op x x) X1 x
         grind)
      | exact superpose f3048_12 f3048_12
      | exact resolve f3048_12 f3048_12
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f3048_129 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X0 (M.op X1 X1)) X3)) = X3 := by
      intro X0 X1 X2 X3
      first
      | (have i₁ := f3048_18 X3 X2 (M.op X1 X1)
         have i₂ := f3048_27 X3 X1 X0
         grind)
      | (have i₁ := f3048_18 X3 X2 (M.op X1 X1)
         have i₂ := f3048_27 X0 X1 X3
         grind)
      | exact superpose f3048_27 f3048_18
      | exact resolve f3048_18 f3048_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f3048_355 : ∀ X0 : G, X2 ≠ (M.op (M.op X0 X0) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2)) := by
      intro X0
      first
      | (have i₁ := f3048_20
         have i₂ := f3048_23 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X2) X0 X3
         grind)
      | exact superpose f3048_23 f3048_20
      | exact resolve f3048_20 f3048_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f3048_356 : False := by
      first
      | (have r₁ := f3048_355 x
         have r₂ := f3048_129 (M.op X0 X0) X1 x X2
         grind)
      | exact resolve f3048_355 f3048_129
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f3048_356
  clear eq374
  have eq5035 : ∀ X0 X1 : G, (M.op (σ x) (σ (k X0 X0))) = (M.op (M.op (σ (k X0 X0)) X1) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | exact superpose eq730 eq373
    | (have j1 := eq730 X0
       grind)
    | exact resolve eq373 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373 eq730
  have eq5961 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq91 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq91
    | (have j0 := eq91 y
       grind)
    | exact resolve eq91 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq5976 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5961
  have eq5980 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5976
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq5976
    | exact resolve eq5976 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq5976
  have eq8818 : ∀ X0 X1 : G, (σ (k X1 X1)) = (M.op X0 (M.op (σ (k X1 X1)) (σ (k X1 X1)))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq728 X1 x (σ (k X1 X1))
       have i₂ := eq359 X0 (σ (k X1 X1)) x
       grind)
    | (have i₁ := eq728 X0 X1 (σ (k X0 X0))
       have i₂ := eq359 (M.op X1 X1) (σ (k X0 X0)) x
       grind)
    | exact superpose eq359 eq728
    | (have j0 := eq728 X1 X1 x
       grind)
    | exact resolve eq728 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8856 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (M.op (σ (k X0 X0)) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq496 (σ (k X0 X0)) (M.op (σ (k X0 X0)) (σ (k X0 X0)))
       have i₂ := eq728 X0 (M.op (σ (k X0 X0)) (σ (k X0 X0))) (σ (k X0 X0))
       grind)
    | exact superpose eq728 eq496
    | (have j1 := eq728 X0 x x
       grind)
    | exact resolve eq496 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496 eq728
  have eq9183 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (k X1 (M.op X1 X1))) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X1) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq457 X1 x
       have i₂ := eq581 X0 X1 x
       grind)
    | (have i₁ := eq457 X1 X1
       have i₂ := eq581 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq581 eq457
    | (have j0 := eq457 X1 X1
       have j1 := eq581 X0 X1 x
       grind)
    | exact resolve eq457 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457 eq581
  have eq9318 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (k X1 (M.op X1 X1))) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq9183 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9183
  have eq11210 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (k (σ y) (σ (M.op x y))) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq90 eq706
    | (have j0 := eq706 y (M.op x y) x
       grind)
    | exact resolve eq706 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq706
  have eq11390 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (k (σ y) (σ (M.op x y))) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11210 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11210
    | (have j0 := eq11210 X0
       grind)
    | exact resolve eq11210 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11210
  have eq11482 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (M.op X0 X0) (M.op (k (σ y) (σ (M.op x y))) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11390 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11390
    | (have j0 := eq11390 X0
       grind)
    | exact resolve eq11390 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11390
  have eq11569 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (M.op X0 X0) (M.op (k (σ y) (σ (M.op x y))) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq21 eq11482
    | (have j0 := eq11482 X0
       grind)
    | exact resolve eq11482 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11482
  have eq11652 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (M.op X0 X0) (M.op (k (σ y) (σ (M.op x y))) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq11569 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11569
    | (have j0 := eq11569 X0
       grind)
    | exact resolve eq11569 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11569
  have eq11734 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (k (σ y) (σ (M.op x y))) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq21 eq11652
    | (have j0 := eq11652 X0
       grind)
    | exact resolve eq11652 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11652
  have eq26162 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq81 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26163 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq26162
    | exact resolve eq26162 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26162
  have eq26174 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq26163
       have r₂ := eq28
       grind)
    | exact resolve eq26163 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26163
  have eq26176 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26174 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq26174
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq26174
       grind)
    | exact resolve eq13 eq26174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26174
  have eq26192 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq26176
  have eq26197 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by grind
  have eq26261 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq26192 eq1187
    | exact resolve eq1187 eq26192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26192
  have eq26333 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq26197
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq26197
       have r₂ := eq13 x y
       grind)
    | exact resolve eq26197 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26197
  have eq26484 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq27 eq26261
    | (have j0 := eq26261 (σ x) X0
       grind)
    | exact resolve eq26261 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26261
  have eq28364 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq81 eq26333
    | exact resolve eq26333 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26333
  have eq28383 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq28364
  have eq28390 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28383 eq26484
    | exact resolve eq26484 eq28383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26484 eq28383
  have eq28498 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq28390
  have eq28504 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq28498
       have r₂ := eq28
       grind)
    | exact resolve eq28498 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28498
  have eq28513 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq28504 eq81
    | exact resolve eq81 eq28504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq28504
  have eq28526 : y = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq28513
  have eq28813 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op y y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq28526
       grind)
    | exact superpose eq28526 eq14
    | exact resolve eq14 eq28526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28526
  have eq32792 : ∀ X0 : G, y = (M.op X0 (M.op y y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq28813 x
       have i₂ := eq359 X0 y x
       grind)
    | (have i₁ := eq28813 X0
       have i₂ := eq359 (M.op X0 X0) y x
       grind)
    | exact superpose eq359 eq28813
    | exact resolve eq28813 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq32933 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq1187 X0 (M.op y y) x
       have i₂ := eq28813 y
       grind)
    | exact superpose eq28813 eq1187
    | exact resolve eq1187 eq28813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28813
  have eq33756 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq32933 x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq32933
    | (have j0 := eq32933 x X0
       grind)
    | exact resolve eq32933 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32933
  have eq34361 : ∀ X0 : G, y = (M.op X0 (M.op x y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq32792 X0
       have i₂ := eq33756 y
       grind)
    | exact superpose eq33756 eq32792
    | exact resolve eq32792 eq33756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32792 eq33756
  have eq34372 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq34361 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34361
  have eq34523 : ∀ X0 X1 X2 : G, y = (M.op X0 (M.op X1 y)) ∨ y = (M.op X2 (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1 X2
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f34523_13 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
      intro X0 X1 X2
      grind
    have f34523_14 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
      intro X0
      grind
    have f34523_23 : y ≠ (M.op X2 (M.op x y)) := by grind
    have f34523_24 : (σ (M.op x y)) ≠ (σ x) := by grind
    have f34523_26 : ∀ X0 : G, y = (M.op X0 (M.op x y)) ∨ y = (M.op x x) := by
      intro X0
      first
      | (have j0 := f34523_14 X0
         grind)
      | (have r₁ := f34523_14 X0
         have r₂ := f34523_24
         grind)
      | exact resolve f34523_14 f34523_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f34523_41 : y ≠ y ∨ y = (M.op x x) := by
      first
      | (have i₁ := f34523_23
         have i₂ := f34523_26 X2
         grind)
      | exact superpose f34523_26 f34523_23
      | (have r₁ := f34523_23
         have r₂ := f34523_26 X2
         grind)
      | exact resolve f34523_23 f34523_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f34523_42 : y = (M.op x x) := by grind
    have f34523_46 : ∀ X0 X1 : G, y = (M.op X0 (M.op X1 y)) := by
      intro X0 X1
      first
      | (have i₁ := f34523_13 X0 x x
         have i₂ := f34523_42
         grind)
      | exact superpose f34523_42 f34523_13
      | exact resolve f34523_13 f34523_42
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f34523_72 : y ≠ y := by
      first
      | (have i₁ := f34523_23
         have i₂ := f34523_46 X2 x
         grind)
      | exact superpose f34523_46 f34523_23
      | (have r₁ := f34523_23
         have r₂ := f34523_46 X2 x
         grind)
      | exact resolve f34523_23 f34523_46
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f34523_73 : False := by grind
    exact f34523_73
  clear eq1294 eq34372
  have eq41002 : ∀ X0 X1 : G, y = (M.op X1 (M.op x y)) ∨ y = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq34523 X1 x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq34523
    | (have j0 := eq34523 X1 x X1
       grind)
    | exact resolve eq34523 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34523
  have eq41495 : ∀ X0 : G, y ≠ y ∨ y = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq41002 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41002
  have eq41496 : ∀ X0 : G, y = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq41495 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41495
  have eq41546 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 X1) X0)) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq41496 eq14
    | exact resolve eq14 eq41496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41612 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq41496 eq1187
    | exact resolve eq1187 eq41496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41644 : ∀ X0 : G, y ≠ X0 ∨ (M.op x y) = (k (M.op x y) X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq41496 eq13
    | (have j0 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq41496 y
       grind)
    | exact resolve eq13 eq41496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41730 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq41496 eq153
    | exact resolve eq153 eq41496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41757 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq41730
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq41730
    | exact resolve eq41730 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41730
  have eq42052 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq41612 x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq41612
    | (have j0 := eq41612 x X0
       grind)
    | exact resolve eq41612 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq41612
  have eq42905 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq1187 X0 y x
       have i₂ := eq42052 y
       grind)
    | exact superpose eq42052 eq1187
    | exact resolve eq1187 eq42052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43012 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq110
       have i₂ := eq42052 y
       grind)
    | exact superpose eq42052 eq110
    | exact resolve eq110 eq42052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq43062 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq43012
    | exact resolve eq43012 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43012
  have eq45070 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 (M.op x y))) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq42905 eq153
    | exact resolve eq153 eq42905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq42905
  have eq46750 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq41757 eq152
    | exact resolve eq152 eq41757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41757
  have eq46792 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq30 eq46750
    | exact resolve eq46750 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq46750
  have eq47547 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq5980 eq43062
    | exact resolve eq43062 eq5980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5980
  have eq48384 : ∀ X0 : G, (M.op y (M.op (M.op x y) X0)) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq41546 X0 y
       have i₂ := eq42052 X0
       grind)
    | (have i₁ := eq41546 x y
       have i₂ := eq42052 X0
       grind)
    | exact superpose eq42052 eq41546
    | exact resolve eq41546 eq42052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42052
  have eq48391 : ∀ X0 : G, (M.op y (M.op y X0)) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f48391_13 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 X1) X0)) = X0 ∨ (σ (M.op x y)) = (σ x) := by
      intro X0 X1
      grind
    have f48391_14 : ∀ X0 : G, y = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
      intro X0
      grind
    have f48391_22 : X0 ≠ (M.op y (M.op y X0)) := by grind
    have f48391_24 : (σ (M.op x y)) ≠ (σ x) := by grind
    have f48391_26 : ∀ X0 : G, y = (M.op X0 (M.op x y)) := by
      intro X0
      first
      | (have j0 := f48391_14 X0
         grind)
      | (have r₁ := f48391_14 X0
         have r₂ := f48391_24
         grind)
      | exact resolve f48391_14 f48391_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f48391_27 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 X1) X0)) = X0 := by
      intro X0 X1
      first
      | (have j0 := f48391_13 X0 X1
         grind)
      | (have r₁ := f48391_13 X0 X1
         have r₂ := f48391_24
         grind)
      | exact resolve f48391_13 f48391_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f48391_28 : ∀ X0 : G, (M.op y (M.op y X0)) = X0 := by
      intro X0
      first
      | (have i₁ := f48391_27 X0 (M.op x y)
         have i₂ := f48391_26 X0
         grind)
      | exact superpose f48391_26 f48391_27
      | exact resolve f48391_27 f48391_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f48391_33 : X0 ≠ X0 := by
      first
      | (have i₁ := f48391_22
         have i₂ := f48391_28 X0
         grind)
      | exact superpose f48391_28 f48391_22
      | (have r₁ := f48391_22
         have r₂ := f48391_28 X0
         grind)
      | exact resolve f48391_22 f48391_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f48391_35 : False := by grind
    exact f48391_35
  clear eq41546
  have eq48812 : ∀ X0 : G, (M.op y (M.op y X0)) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq48391 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48391
  have eq48819 : ∀ X0 : G, (M.op y (M.op (M.op x y) X0)) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq48384 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48384
  have eq49752 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op y X0) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq48819 eq48812
    | exact resolve eq48812 eq48819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48812 eq48819
  have eq49806 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op y X0) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq49752 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49752
  have eq50061 : ∀ X0 : G, (M.op x y) ≠ (M.op y X0) ∨ (k X0 (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq49806 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | exact resolve eq13 eq49806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49806
  have eq1292557 : ∀ X0 : G, (τ (k (σ (M.op x y)) (σ (M.op x y)))) = (M.op X0 (M.op x y)) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq45070 eq16
    | (have j1 := eq45070 X0
       grind)
    | exact resolve eq16 eq45070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45070
  have eq1292868 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op X0 (M.op x y)) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq152 eq1292557
    | (have j0 := eq1292557 X0
       grind)
    | exact resolve eq1292557 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292557
  have eq1293271 : ∀ X0 : G, y = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1292868 eq41496
    | (have j1 := eq1292868 X0
       grind)
    | exact resolve eq41496 eq1292868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41496 eq1292868
  have eq1294310 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq1293271 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293271
  have eq1296289 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1294310 eq50061
    | (have j0 := eq50061 (M.op x y)
       grind)
    | (have r₁ := eq50061 (M.op x y)
       have r₂ := eq1294310 y
       grind)
    | exact resolve eq50061 eq1294310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50061 eq1294310
  have eq1296438 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k (M.op x y) (M.op x y)) := by grind
  clear eq1296289
  have eq1296439 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k (M.op x y) (M.op x y)) := by grind
  clear eq1296438
  have eq1297161 : y ≠ (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k (M.op x y) (M.op x y)) := by grind
  clear eq1296439
  have eq1297239 : y = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1297161
       have r₂ := eq46792
       grind)
    | exact resolve eq1297161 eq46792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46792 eq1297161
  have eq1297684 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1297239 eq129
    | exact resolve eq129 eq1297239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1297730 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1297239 eq721
    | (have j0 := eq721 (M.op x y)
       grind)
    | exact resolve eq721 eq1297239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1297757 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1297239 eq5035
    | (have j0 := eq5035 (M.op x y) x
       grind)
    | exact resolve eq5035 eq1297239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5035
  have eq1297861 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1297239 eq8818
    | (have j0 := eq8818 X0 (M.op x y)
       grind)
    | exact resolve eq8818 eq1297239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8818
  have eq1297864 : (σ y) = (k (σ y) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1297239 eq8856
    | (have j0 := eq8856 (M.op x y)
       grind)
    | exact resolve eq8856 eq1297239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8856
  have eq1298000 : (σ y) = (k (σ y) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1297864
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1297864
    | exact resolve eq1297864 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297864
  have eq1298003 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq1297861 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1297861
    | (have j0 := eq1297861 X0
       grind)
    | exact resolve eq1297861 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297861
  have eq1298103 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq1297757 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1297757
    | (have j0 := eq1297757 X0
       grind)
    | exact resolve eq1297757 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297757
  have eq1298129 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq1297730
    | exact resolve eq1297730 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297730
  have eq1298170 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1297684
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1297684
    | exact resolve eq1297684 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297684
  have eq1298218 : (σ y) = (k (σ y) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq1298000
    | exact resolve eq1298000 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298000
  have eq1298221 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq21 eq1298003
    | (have j0 := eq1298003 X0
       grind)
    | exact resolve eq1298003 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298003
  have eq1298321 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq27 eq1298103
    | (have j0 := eq1298103 X0
       grind)
    | exact resolve eq1298103 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298103
  have eq1298347 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1298129
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1298129
    | exact resolve eq1298129 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298129
  have eq1298444 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq21 eq1298321
    | (have j0 := eq1298321 X0
       grind)
    | exact resolve eq1298321 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298321
  have eq1298454 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq1298347
    | exact resolve eq1298347 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298347
  have eq1369179 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1298221 eq1298444
    | exact resolve eq1298444 eq1298221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298221 eq1298444
  have eq1369936 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1369179
  have eq1369971 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1369936 eq1298218
    | exact resolve eq1298218 eq1369936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298218
  have eq1370842 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1369971
  have eq1716075 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1369936 eq47547
    | exact resolve eq47547 eq1369936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47547 eq1369936
  have eq1717058 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq1716075
  have eq1717077 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1717058
       have r₂ := eq28
       grind)
    | exact resolve eq1717058 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717058
  have eq1721703 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1717077 eq13
    | (have j0 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq1717077
       grind)
    | exact resolve eq13 eq1717077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717077
  have eq1721922 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1721703
  have eq1725059 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1721922 eq152
    | exact resolve eq152 eq1721922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1721922
  have eq1725540 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq1725059
    | exact resolve eq1725059 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1725059
  have eq1725543 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq41644 (M.op x y)
       grind)
    | (have r₁ := eq1725540
       have r₂ := eq41644 (M.op x y)
       grind)
    | exact resolve eq1725540 eq41644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1725540
  have eq1725551 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1725543 eq129
    | exact resolve eq129 eq1725543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1725581 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1725543 eq1297239
    | exact resolve eq1297239 eq1725543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297239
  have eq1725645 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1725543 eq721
    | (have j0 := eq721 (M.op x y)
       grind)
    | exact resolve eq721 eq1725543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721 eq1725543
  have eq1725998 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1725645
  have eq1726033 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq1725581
  have eq1726231 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1725998
    | exact resolve eq1725998 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1725998
  have eq1726275 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1725551
    | exact resolve eq1725551 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1725551
  have eq1726592 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1726033 eq28
    | exact resolve eq28 eq1726033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726033
  have eq1731479 : ∀ X0 X1 : G, (M.op X0 (σ (M.op x y))) = (M.op X1 (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1726231 eq1187
    | exact resolve eq1187 eq1726231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1732399 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1726275 eq1298170
    | exact resolve eq1298170 eq1726275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726275
  have eq1732804 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1732399
  have eq1733122 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1732804 eq1370842
    | exact resolve eq1370842 eq1732804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370842 eq1732804
  have eq1733127 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1733122
  have eq1733358 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1733127
       have r₂ := eq1298454
       grind)
    | exact resolve eq1733127 eq1298454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298454 eq1733127
  have eq1780613 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1731479 eq1726231
    | exact resolve eq1726231 eq1731479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726231 eq1731479
  have eq1780702 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1780613 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1780613
  have eq1806699 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1733358 eq43062
    | exact resolve eq43062 eq1733358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43062 eq1733358
  have eq1807088 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq1806699
  have eq1807109 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1807088
       have r₂ := eq1726592
       grind)
    | exact resolve eq1807088 eq1726592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726592 eq1807088
  have eq1807793 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1807109 eq13
    | (have j0 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq1807109
       grind)
    | exact resolve eq13 eq1807109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1807109
  have eq1808014 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq1807793
  have eq1808120 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1808014 eq152
    | exact resolve eq152 eq1808014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq1808014
  have eq1808610 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq1808120
    | exact resolve eq1808120 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1808120
  have eq1808616 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have j1 := eq41644 (M.op x y)
       grind)
    | (have r₁ := eq1808610
       have r₂ := eq41644 (M.op x y)
       grind)
    | exact resolve eq1808610 eq41644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41644 eq1808610
  have eq1810131 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1808616 eq129
    | exact resolve eq129 eq1808616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq1808616
  have eq1810869 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq1810131
    | exact resolve eq1810131 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1810131
  have eq1815961 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1810869 eq1298170
    | exact resolve eq1298170 eq1810869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298170 eq1810869
  have eq1816370 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1815961
  have eq1816411 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1816370 eq27
    | exact resolve eq27 eq1816370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1829926 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1816411 eq1780702
    | exact resolve eq1780702 eq1816411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1780702 eq1816411
  have eq1830157 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1829926
  have eq1830237 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1830157
       have r₂ := eq28
       grind)
    | exact resolve eq1830157 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1830157
  have eq1834576 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1830237 eq28
    | exact resolve eq28 eq1830237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1830237
  have eq1835088 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1834576
       have r₂ := eq1816370
       grind)
    | exact resolve eq1834576 eq1816370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1816370 eq1834576
  have eq1835089 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1835088 eq27
    | exact resolve eq27 eq1835088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1835090 : x = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq1835088 eq29
    | exact resolve eq29 eq1835088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1835388 : x = (M.op x y) := by
    first
    | exact superpose eq31 eq1835090
    | exact resolve eq1835090 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1835090
  have eq1835392 : x ≠ x ∨ y = (k y x) := by
    first
    | exact superpose eq1835388 eq51
    | (have r₁ := eq51
       have r₂ := eq1835388
       grind)
    | exact resolve eq51 eq1835388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1835467 : ∀ X0 X1 : G, (M.op x (M.op (M.op x x) X0)) = (M.op (M.op X1 X1) (M.op (M.op x x) X0)) := by
    intro X0 X1
    first
    | exact superpose eq1835388 eq1007
    | exact resolve eq1007 eq1835388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1835477 : ∀ X0 X1 : G, x = (M.op x (M.op (M.op X0 (M.op X1 X1)) x)) := by
    intro X0 X1
    first
    | exact superpose eq1835388 eq1553
    | exact resolve eq1553 eq1835388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553
  have eq1836049 : y = (k y x) := by grind
  clear eq1835392
  have eq1836142 : x = (M.op x (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq1835477 x x
       have i₂ := eq1246 x x
       grind)
    | exact superpose eq1246 eq1835477
    | exact resolve eq1835477 eq1246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246 eq1835477
  have eq1836148 : ∀ X0 : G, (M.op x (M.op (M.op x x) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1835467 X0 x
       have i₂ := eq380 x X0 x
       grind)
    | exact superpose eq380 eq1835467
    | exact resolve eq1835467 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq1835467
  have eq1836246 : x = (M.op x (M.op x x)) := by
    first
    | exact superpose eq1835388 eq1836142
    | exact resolve eq1836142 eq1835388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835388 eq1836142
  have eq1841090 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq88
       have i₂ := eq1836049
       grind)
    | exact superpose eq1836049 eq88
    | exact resolve eq88 eq1836049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq1836049
  have eq1841276 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1835088 eq1841090
    | exact resolve eq1841090 eq1835088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835088 eq1841090
  have eq1841365 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1841276
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1841276
    | exact resolve eq1841276 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1841276
  have eq1841843 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1841365 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq1841365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1841895 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1835089 eq1841843
    | exact resolve eq1841843 eq1835089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1841843
  have eq1841920 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq1841895
       have r₂ := eq28
       grind)
    | exact resolve eq1841895 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1841895
  have eq1850229 : ∀ X0 : G, x = (M.op X0 (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq1836246
       have i₂ := eq1187 x x X0
       grind)
    | (have i₁ := eq1836246
       have i₂ := eq1187 X0 x x
       grind)
    | exact superpose eq1187 eq1836246
    | exact resolve eq1836246 eq1187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1850254 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1235 x x X0 X1
       have i₂ := eq1836246
       grind)
    | exact superpose eq1836246 eq1235
    | exact resolve eq1235 eq1836246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235
  have eq1850257 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1241 x x X0 X1
       have i₂ := eq1836246
       grind)
    | exact superpose eq1836246 eq1241
    | exact resolve eq1241 eq1836246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq1850261 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1248 x x X0 X1
       have i₂ := eq1836246
       grind)
    | exact superpose eq1836246 eq1248
    | exact resolve eq1248 eq1836246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248 eq1836246
  have eq1869279 : (M.op (k (σ y) (σ (M.op x y))) (σ y)) = (M.op x (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq11734 eq1836148
    | exact resolve eq1836148 eq11734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11734 eq1836148
  have eq1869869 : (M.op (σ y) (σ y)) = (M.op x (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1841365 eq1869279
    | exact resolve eq1869279 eq1841365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869279
  have eq1869957 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op x (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1835089 eq1869869
    | exact resolve eq1869869 eq1835089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869869
  have eq1869993 : (M.op (σ y) (σ y)) = (M.op x (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq1869957
       have r₂ := eq28
       grind)
    | exact resolve eq1869957 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869957
  have eq1904805 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1850254 X0 (M.op x x)
       have i₂ := eq1850229 X0
       grind)
    | exact superpose eq1850229 eq1850254
    | exact resolve eq1850254 eq1850229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850229 eq1850254
  have eq2295723 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op x (σ y))) X1) X2) (M.op (M.op (M.op X0 X0) (M.op x (σ y))) X1)) = X1 ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1869993 eq3048
    | exact resolve eq3048 eq1869993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3048
  have eq2296502 : (σ (M.op x y)) ≠ (M.op x (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq1869993
  have eq2296972 : ∀ X0 X1 : G, (M.op x (M.op (M.op (M.op X0 X0) (M.op x (σ y))) X1)) = X1 ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2295723 X0 X1 X1
       have i₂ := eq1850257 (M.op (M.op (M.op X0 X0) (M.op x sF3)) X1) X1
       grind)
    | exact superpose eq1850257 eq2295723
    | exact resolve eq2295723 eq1850257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850257 eq2295723
  have eq2297275 : ∀ X1 : G, (M.op x (M.op (M.op x (M.op x (σ y))) X1)) = X1 ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq2296972 X1 X1
       have i₂ := eq1850261 (M.op x sF3) X1
       grind)
    | exact superpose eq1850261 eq2296972
    | exact resolve eq2296972 eq1850261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850261 eq2296972
  have eq2297395 : ∀ X1 : G, (M.op x (M.op (σ y) X1)) = X1 ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq2297275 X1
       have i₂ := eq1904805 sF3
       grind)
    | exact superpose eq1904805 eq2297275
    | exact resolve eq2297275 eq1904805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1904805 eq2297275
  have eq2308875 : (σ (M.op x y)) = (M.op x (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1841920 eq2297395
    | exact resolve eq2297395 eq1841920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1841920 eq2297395
  have eq2309350 : (σ (M.op x y)) = (M.op x (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq2308875
  have eq2309500 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq2309350
       have r₂ := eq2296502
       grind)
    | exact resolve eq2309350 eq2296502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2296502 eq2309350
  have eq2310626 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (k (σ y) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq2309500 eq9318
    | exact resolve eq9318 eq2309500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9318 eq2309500
  have eq2311446 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq1841365 eq2310626
    | exact resolve eq2310626 eq1841365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1841365 eq2310626
  have eq2311977 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq1835089 eq2311446
    | (have j0 := eq2311446 (σ x)
       grind)
    | exact resolve eq2311446 eq1835089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835089 eq2311446
  have eq2312323 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq2311977 X0
       grind)
    | (have r₁ := eq2311977 X0
       have r₂ := eq28
       grind)
    | (have r₁ := eq2311977 (σ x)
       have r₂ := eq28
       grind)
    | exact resolve eq2311977 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2311977
  have eq2322944 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2312323 eq27
    | (have j1 := eq2312323 (σ x)
       grind)
    | exact resolve eq27 eq2312323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2312323
  have eq2323007 : False := by grind
  exact eq2323007
