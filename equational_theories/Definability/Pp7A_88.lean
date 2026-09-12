import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxy_y_pxy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
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
  clear eq22
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq50 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq14 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
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
  have eq59 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | (have r₁ := eq11 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq72 x y
       grind)
    | exact superpose eq72 eq44
    | (have j1 := eq72 x y
       grind)
    | exact resolve eq44 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55
       have i₂ := eq72 sF2 sF3
       grind)
    | exact superpose eq72 eq55
    | (have j1 := eq72 (σ x) (σ y)
       grind)
    | exact resolve eq55 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq88 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq87
    | exact resolve eq87 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq83
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq83
    | exact resolve eq83 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq88
    | exact resolve eq88 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq90
    | exact resolve eq90 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq97 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq94 eq72
    | (have j0 := eq72 (σ x) (σ y)
       grind)
    | exact resolve eq72 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq98 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq97
    | exact resolve eq97 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq101 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq98
       have r₂ := eq27
       grind)
    | exact resolve eq98 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq103 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq101
    | exact resolve eq101 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq105 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq103 eq27
    | exact resolve eq27 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : y ≠ (M.op x y) ∨ (M.op x x) = (M.op y y) ∨ (k x y) = (M.op y y) := by
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
  have eq107 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq120 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq123 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq119
       have i₂ := eq61 sF3
       grind)
    | exact superpose eq61 eq119
    | exact resolve eq119 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq125 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq123
       have i₂ := eq61 y
       grind)
    | exact superpose eq61 eq123
    | exact resolve eq123 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq456 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq50 X1 X0 X3
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op (M.op X0 (M.op y y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq50 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y X0 x
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op (M.op X0 (M.op (σ y) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq50
    | (have j0 := eq50 (σ y) X0 (σ x)
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq489 : (k (σ x) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq44
    | exact resolve eq44 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq92
  have eq492 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq489
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq489
    | exact resolve eq489 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq577 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq103 eq107
    | (have r₁ := eq107
       have r₂ := eq103
       grind)
    | exact resolve eq107 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq578 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq577
  have eq583 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq578 eq94
    | exact resolve eq94 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq586 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq583
  have eq596 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq586 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq586
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq586
       grind)
    | exact resolve eq13 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq881 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j0 := eq596 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq886 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq881
    | exact resolve eq881 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq881
  have eq904 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq886 eq94
    | exact resolve eq94 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq886
  have eq907 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq904
  have eq911 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq907
       have r₂ := eq27
       grind)
    | exact resolve eq907 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907
  have eq919 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X1 (σ (M.op x y))))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq911 eq14
    | exact resolve eq14 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq920 : ∀ X0 X1 : G, (M.op X0 (σ (M.op x y))) = (M.op (M.op X0 (σ (M.op x y))) (M.op X1 (σ y))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq911 eq50
    | exact resolve eq50 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq928 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op (M.op X0 (σ (M.op x y))) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq911 eq458
    | exact resolve eq458 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq1016 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq103 eq928
    | exact resolve eq928 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq928
  have eq1019 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1016 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq1170 : ∀ X0 X1 : G, (M.op X1 (σ (M.op x y))) = (M.op (M.op X1 (σ (M.op x y))) (M.op X0 (σ (M.op x y)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1019 eq920
    | exact resolve eq920 eq1019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920 eq1019
  have eq1191 : ∀ X0 X1 : G, (M.op X1 (σ (M.op x y))) = (M.op (M.op X1 (σ (M.op x y))) (M.op X0 (σ (M.op x y)))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq1170 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170
  have eq1262 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ (M.op x y)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1191 eq919
    | exact resolve eq919 eq1191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191
  have eq1276 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ (M.op x y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1262 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262
  have eq1322 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1276 eq919
    | exact resolve eq919 eq1276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919 eq1276
  have eq1328 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1322
  have eq1334 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1328 eq911
    | exact resolve eq911 eq1328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911 eq1328
  have eq1351 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq1334
  have eq1358 : y = (M.op x y) := by
    first
    | (have r₁ := eq1351
       have r₂ := eq105
       grind)
    | exact resolve eq1351 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq1351
  have eq1361 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1358 eq20
    | exact resolve eq20 eq1358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1363 : y ≠ y ∨ (M.op x x) = (M.op y y) ∨ (k x y) = (M.op y y) := by
    first
    | exact superpose eq1358 eq106
    | (have r₁ := eq106
       have r₂ := eq1358
       grind)
    | exact resolve eq106 eq1358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq1372 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op (M.op X0 (M.op y y)) y) := by
    intro X0
    first
    | exact superpose eq1358 eq457
    | exact resolve eq457 eq1358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq1373 : (M.op x x) = (M.op y y) ∨ (k x y) = (M.op y y) := by grind
  clear eq1363
  have eq1383 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1361
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1361
    | exact resolve eq1361 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1361
  have eq1460 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1383 eq492
    | exact resolve eq492 eq1383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq1477 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq1460
       have r₂ := eq27
       grind)
    | exact resolve eq1460 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460
  have eq1502 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1477 eq59
    | exact resolve eq59 eq1477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq1504 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1358 eq1502
    | exact resolve eq1502 eq1358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1502
  have eq6323 : (M.op x x) = (M.op y y) ∨ (τ (M.op (σ x) (σ y))) = (M.op y y) := by
    first
    | (have i₁ := eq1373
       have i₂ := eq1504
       grind)
    | exact superpose eq1504 eq1373
    | exact resolve eq1373 eq1504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373 eq1504
  have eq8018 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) (M.op x y))) = (M.op (M.op X0 (M.op (M.op x y) (M.op x y))) (M.op X1 (M.op y y))) := by
    intro X0 X1
    first
    | (have i₁ := eq456 X1 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq456
    | (have j0 := eq456 X1 y X0 x
       grind)
    | exact resolve eq456 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq8095 : ∀ X0 X1 : G, (M.op X0 (M.op y y)) = (M.op (M.op X0 (M.op y y)) (M.op X1 (M.op y y))) := by
    intro X0 X1
    first
    | exact superpose eq1358 eq8018
    | exact resolve eq8018 eq1358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8018
  have eq13321 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq14 y (M.op X0 (M.op y y)) x
       have i₂ := eq8095 X0 x
       grind)
    | exact superpose eq8095 eq14
    | exact resolve eq14 eq8095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8095
  have eq13373 : y = (M.op y y) := by
    first
    | (have i₁ := eq14 y y x
       have i₂ := eq13321 x
       grind)
    | exact superpose eq13321 eq14
    | exact resolve eq14 eq13321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13395 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq125
       have i₂ := eq13373
       grind)
    | exact superpose eq13373 eq125
    | exact resolve eq125 eq13373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq13408 : ∀ X0 : G, y = (M.op y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq13321 X0
       have i₂ := eq13373
       grind)
    | exact superpose eq13373 eq13321
    | exact resolve eq13321 eq13373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13321
  have eq13436 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1383 eq13395
    | exact resolve eq13395 eq1383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13395
  have eq13444 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq13436
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13436
    | exact resolve eq13436 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13436
  have eq13449 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1383 eq13444
    | exact resolve eq13444 eq1383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13444
  have eq13753 : y = (M.op y (M.op x x)) ∨ (τ (M.op (σ x) (σ y))) = (M.op y y) := by
    first
    | (have i₁ := eq13408 y
       have i₂ := eq6323
       grind)
    | exact superpose eq6323 eq13408
    | exact resolve eq13408 eq6323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6323 eq13408
  have eq13777 : y = (M.op y (M.op x x)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13753
       have i₂ := eq13373
       grind)
    | exact superpose eq13373 eq13753
    | exact resolve eq13753 eq13373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13373 eq13753
  have eq17621 : ∀ X0 : G, x = (M.op x (M.op X0 y)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq13777
       grind)
    | exact superpose eq13777 eq14
    | exact resolve eq14 eq13777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13777
  have eq18029 : x = (M.op x y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1372 x
       have i₂ := eq17621 y
       grind)
    | exact superpose eq17621 eq1372
    | exact resolve eq1372 eq17621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372 eq17621
  have eq18038 : x = (M.op x y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18029
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18029
    | exact resolve eq18029 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq18029
  have eq18054 : y = (τ (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq1358 eq18038
    | exact resolve eq18038 eq1358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358 eq18038
  have eq18080 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq18054 eq15
    | exact resolve eq15 eq18054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18054
  have eq18174 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq18080
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18080
    | exact resolve eq18080 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq18080
  have eq18214 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1383 eq18174
    | exact resolve eq18174 eq1383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18174
  have eq18243 : x = y := by
    first
    | (have r₁ := eq18214
       have r₂ := eq27
       grind)
    | exact resolve eq18214 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18214
  have eq18272 : (σ (k x (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq120
       have i₂ := eq18243
       grind)
    | exact superpose eq18243 eq120
    | exact resolve eq120 eq18243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq18243
  have eq18386 : (σ (k x (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1383 eq18272
    | exact resolve eq18272 eq1383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1383 eq18272
  have eq18407 : (σ (k x (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq18386
       have i₂ := eq61 sF1
       grind)
    | exact superpose eq61 eq18386
    | exact resolve eq18386 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq18386
  have eq18423 : (σ (M.op x y)) = (σ (k x (M.op x y))) := by
    first
    | exact superpose eq13449 eq18407
    | exact resolve eq18407 eq13449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13449 eq18407
  have eq18429 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq45 eq18423
    | exact resolve eq18423 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq18423
  have eq18432 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1477 eq18429
    | exact resolve eq18429 eq1477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477 eq18429
  have eq18433 : False := by grind
  exact eq18433

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq66 (σ X0)
       grind)
    | exact superpose eq66 eq15
    | exact resolve eq15 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq66 (τ X0)
       grind)
    | exact superpose eq66 eq32
    | exact resolve eq32 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq78 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq71
    | exact resolve eq71 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq80 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq69
    | exact resolve eq69 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq69
  have eq95 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq529 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq554 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq529 X0 X1
       have i₂ := eq80 X1
       grind)
    | exact superpose eq80 eq529
    | (have j0 := eq529 X0 X1
       grind)
    | exact resolve eq529 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq568 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq554 X0 X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq554
    | (have j0 := eq554 X0 X1
       grind)
    | exact resolve eq554 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq581 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq568 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq568
    | (have j0 := eq568 (τ X0) X1
       grind)
    | exact resolve eq568 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq597 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq581 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq581
    | (have j0 := eq581 X0 X1
       grind)
    | exact resolve eq581 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq603 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (σ (M.op X1 X1)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq597 X0 X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq597
    | (have j0 := eq597 X0 X1
       grind)
    | exact resolve eq597 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq597
  have eq607 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq603 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq603
    | (have j0 := eq603 X0 X1
       grind)
    | exact resolve eq603 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq609 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq607 X0 X1
       have j1 := eq95 X1 X0
       grind)
    | (have r₁ := eq607 X1 X0
       have r₂ := eq95 X0 X1
       grind)
    | (have r₁ := eq607 (M.op X1 X1) (M.op X0 X0)
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq607 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq607
  have eq611 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq609 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq609
    | exact resolve eq609 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq617 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq609 (σ X1) X0
       grind)
    | exact superpose eq609 eq15
    | (have j1 := eq609 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq651 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq611 X0 (τ X1)
       grind)
    | exact superpose eq611 eq19
    | (have j1 := eq611 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq611
  have eq795 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq651 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq651
    | exact resolve eq651 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq846 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq795 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq795
    | (have j0 := eq795 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq795 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq990 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq617 x y
       grind)
    | exact superpose eq617 eq16
    | (have j1 := eq617 x y
       grind)
    | exact resolve eq16 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq1007 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq990
       have i₂ := eq846 y x
       grind)
    | exact superpose eq846 eq990
    | (have j1 := eq846 (σ x) (σ y)
       grind)
    | (have r₁ := eq990
       have r₂ := eq846 y x
       grind)
    | (have r₁ := eq990
       have r₂ := eq846 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq990
       have r₂ := eq846 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq990 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846 eq990
  have eq1008 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1007
  have eq1011 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1008
       grind)
    | exact superpose eq1008 eq16
    | exact resolve eq16 eq1008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1012 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1011
       have r₂ := eq80 x
       grind)
    | exact resolve eq1011 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq1013 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1012
       grind)
    | exact superpose eq1012 eq16
    | exact resolve eq16 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1014 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1012
       grind)
    | exact superpose eq1012 eq10
    | exact resolve eq10 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012
  have eq1061 : x = y := by
    first
    | (have i₁ := eq1014
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1014
    | exact resolve eq1014 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq1062 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1013
       have i₂ := eq80 x
       grind)
    | exact superpose eq80 eq1013
    | exact resolve eq1013 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq1013
  have eq1063 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1062
       have i₂ := eq1061
       grind)
    | exact superpose eq1061 eq1062
    | exact resolve eq1062 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061 eq1062
  have eq1064 : False := by grind
  exact eq1064

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_pyy_pxy_pyy_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq28 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq44 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq45 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq28 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq44 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq110 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq289 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq290 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq289 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq295 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq290 X0 X1
       have j1 := eq110 X0 X1
       grind)
    | (have r₁ := eq290 X0 X1
       have r₂ := eq110 X0 X1
       grind)
    | (have r₁ := eq290 X0 X0
       have r₂ := eq110 X0 X0
       grind)
    | exact resolve eq290 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq290
  have eq306 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq295 (σ X0) (σ X1)
       grind)
    | exact superpose eq295 eq15
    | exact resolve eq15 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq306 X0 X1
       have i₂ := eq295 X0 X1
       grind)
    | exact superpose eq295 eq306
    | exact resolve eq306 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq306
  have eq313 : False := by grind
  exact eq313

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_x_pxy_x_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
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
  have eq31 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq37 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X2 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq26
    | exact resolve eq26 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       grind)
    | (have r₁ := eq13 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq43 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq49 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq32
    | exact resolve eq32 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq73 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X0) (τ X0)
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq82 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
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
  have eq162 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 (k X1 (τ X0)) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq71
    | exact resolve eq71 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) (M.op X1 (M.op X2 (σ (k X0 X0))))) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46 (σ X1) X1 X2
       have i₂ := eq71 X1 X1
       grind)
    | exact superpose eq71 eq46
    | (have j0 := eq46 (σ X0) X1 X2
       have j1 := eq71 X0 X0
       grind)
    | exact resolve eq46 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq169 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq71 X0 X0
       grind)
    | exact superpose eq71 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq71 X0 X0
       grind)
    | (have r₁ := eq12 (σ X1) X1
       have r₂ := eq71 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) X1
       have r₂ := eq71 X0 X1
       grind)
    | exact resolve eq12 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq71 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq176 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq175 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq180 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq169 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq182 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) (M.op X1 (M.op X2 (σ (k X0 X0))))) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq167 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq184 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq180 X0 X1
       have j1 := eq12 (σ X0) X1
       grind)
    | (have r₁ := eq180 X0 X1
       have r₂ := eq12 (σ X0) X1
       grind)
    | exact resolve eq180 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq185 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (M.op X1 (M.op X2 (σ (k X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq182 X0 X1 X2
       have j1 := eq176 X0
       grind)
    | (have r₁ := eq182 X0 X1 X2
       have r₂ := eq176 X0
       grind)
    | exact resolve eq182 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq182
  have eq718 : ∀ X0 X1 X2 X3 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (k (σ X0) (M.op X2 (M.op X3 (σ (k X0 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq185 X0 X2 X3
       grind)
    | exact superpose eq185 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq185 X0 X2 X3
       grind)
    | (have r₁ := eq12 (σ X0) X1
       have r₂ := eq185 X0 X1 X2
       grind)
    | exact resolve eq12 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq724 : ∀ X0 X1 X2 X3 : G, (σ X0) = (k (σ X0) (M.op X2 (M.op X3 (σ (k X0 X0))))) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq718 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq862 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq73 X0 (τ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq863 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq862 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq865 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq863 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq863
    | (have j0 := eq863 X0
       grind)
    | exact resolve eq863 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq898 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq865 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq865
    | exact resolve eq865 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq915 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq898 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq898
    | (have j0 := eq898 X0
       grind)
    | exact resolve eq898 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq960 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq82 x X2 X0 X1
       grind)
    | exact superpose eq82 eq9
    | exact resolve eq9 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq1005 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X2 X0
       have i₂ := eq960 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq960 eq9
    | exact resolve eq9 eq960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1063 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq915 X0
       grind)
    | exact superpose eq915 eq10
    | (have j1 := eq915 X0
       grind)
    | exact resolve eq10 eq915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq1103 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1063 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1063
    | (have j0 := eq1063 X0
       grind)
    | exact resolve eq1063 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063
  have eq1109 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1103 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq1103 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq1103 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1115 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq184 X0 X1
       have i₂ := eq1109 X0
       grind)
    | exact superpose eq1109 eq184
    | (have j0 := eq184 X0 X1
       grind)
    | exact resolve eq184 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq1134 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1109 (σ X0)
       grind)
    | exact superpose eq1109 eq15
    | exact resolve eq15 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1140 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq1109 (τ X0)
       grind)
    | exact superpose eq1109 eq35
    | exact resolve eq35 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1150 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1140 X0
       have i₂ := eq1109 X0
       grind)
    | exact superpose eq1109 eq1140
    | exact resolve eq1140 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq1156 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1134 X0
       have i₂ := eq1109 X0
       grind)
    | exact superpose eq1109 eq1134
    | exact resolve eq1134 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq1298 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op X1 (M.op X2 (σ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq1156 X0
       grind)
    | exact superpose eq1156 eq9
    | exact resolve eq9 eq1156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1996 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (k (σ X0) X1) ∨ (k (σ X0) X1) = (k (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k (σ X0) X1) (σ X2)
       have i₂ := eq162 X0 X1 X2
       grind)
    | exact superpose eq162 eq13
    | (have j0 := eq13 (k (σ X0) X1) (σ X2)
       have j1 := eq162 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq162 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (k (σ X0) X1)
       have r₂ := eq162 X0 X1 X2
       grind)
    | exact resolve eq13 eq162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq1997 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (k (σ X0) X1) ∨ (k (σ X0) X1) = (k (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1996 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1996
  have eq1998 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (k (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1997 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1997
  have eq2001 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (k (k X0 (τ X1)) X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1998 X0 X1 X2
       have i₂ := eq31 X0 X1 X2
       grind)
    | exact superpose eq31 eq1998
    | (have j0 := eq1998 X0 X1 X2
       grind)
    | exact resolve eq1998 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1998
  have eq7690 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq960 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) X1 X2
       have i₂ := eq1005 (M.op X1 X2) X0 (M.op X1 X2)
       grind)
    | exact superpose eq1005 eq960
    | exact resolve eq960 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960 eq1005
  have eq14177 : ∀ X0 X1 X2 : G, (σ X0) ≠ (M.op (σ X0) (M.op X1 (M.op X2 (σ (k X0 X0))))) ∨ (k (σ X0) (M.op X1 (M.op X2 (σ (k X0 X0))))) = (M.op (σ X0) (M.op X1 (M.op X2 (σ (k X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq724 X0 (M.op X1 (M.op X2 (σ (k X0 X0)))) X2 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq14185 : ∀ X0 X1 X2 : G, (σ X0) ≠ (M.op (σ X0) (M.op X1 (M.op X2 (σ (M.op X0 X0))))) ∨ (k (σ X0) (M.op X1 (M.op X2 (σ (k X0 X0))))) = (M.op (σ X0) (M.op X1 (M.op X2 (σ (k X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14177 X0 X1 X2
       have i₂ := eq1109 X0
       grind)
    | exact superpose eq1109 eq14177
    | (have j0 := eq14177 X0 X1 X2
       grind)
    | exact resolve eq14177 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14177
  have eq14253 : ∀ X0 X1 X2 : G, (k (σ X0) (M.op X1 (M.op X2 (σ (k X0 X0))))) = (M.op (σ X0) (M.op X1 (M.op X2 (σ (k X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq14185 X0 X1 X2
       grind)
    | (have r₁ := eq14185 X0 X1 X2
       have r₂ := eq1298 X0 X1 X2
       grind)
    | exact resolve eq14185 eq1298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14185
  have eq14310 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op X1 (M.op X2 (σ (M.op X0 X0))))) = (k (σ X0) (M.op X1 (M.op X2 (σ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14253 X0 X1 X2
       have i₂ := eq1109 X0
       grind)
    | exact superpose eq1109 eq14253
    | exact resolve eq14253 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109 eq14253
  have eq14339 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) (M.op X1 (M.op X2 (σ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14310 X0 X1 X2
       have i₂ := eq1298 X0 X1 X2
       grind)
    | exact superpose eq1298 eq14310
    | exact resolve eq14310 eq1298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298 eq14310
  have eq14405 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (σ (τ X0)) (M.op X1 (M.op X2 (σ (τ (M.op X0 X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14339 (τ X0) X1 X2
       have i₂ := eq1150 X0
       grind)
    | exact superpose eq1150 eq14339
    | exact resolve eq14339 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150
  have eq14440 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X2 (σ (M.op X0 X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 X0 (M.op X1 (M.op X2 (σ (M.op X0 X0))))
       have i₂ := eq14339 X0 X1 X2
       grind)
    | exact superpose eq14339 eq32
    | exact resolve eq32 eq14339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14441 : ∀ X0 X1 X2 X3 : G, (τ (k X1 (σ X0))) = (k (τ X1) (k X0 (τ (M.op X2 (M.op X3 (σ (M.op X0 X0))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq37 X0 (M.op X2 (M.op X3 (σ (M.op X0 X0)))) X1
       have i₂ := eq14339 X0 X2 X3
       grind)
    | exact superpose eq14339 eq37
    | exact resolve eq37 eq14339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq14442 : ∀ X0 X1 X2 X3 : G, (τ (k (σ X0) X3)) = (k (k X0 (τ (M.op X1 (M.op X2 (σ (M.op X0 X0)))))) (τ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq49 X0 (M.op X1 (M.op X2 (σ (M.op X0 X0)))) X3
       have i₂ := eq14339 X0 X1 X2
       grind)
    | exact superpose eq14339 eq49
    | exact resolve eq49 eq14339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq14459 : ∀ X0 X1 X2 X3 : G, (k X0 (τ X3)) = (k (k X0 (τ (M.op X1 (M.op X2 (σ (M.op X0 X0)))))) (τ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14442 X0 X1 X2 X3
       have i₂ := eq32 X0 X3
       grind)
    | exact superpose eq32 eq14442
    | exact resolve eq14442 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14442
  have eq14460 : ∀ X0 X1 X2 X3 : G, (k (τ X1) X0) = (k (τ X1) (k X0 (τ (M.op X2 (M.op X3 (σ (M.op X0 X0))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14441 X0 X1 X2 X3
       have i₂ := eq26 X1 X0
       grind)
    | exact superpose eq26 eq14441
    | exact resolve eq14441 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14441
  have eq14461 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X2 (σ (M.op X0 X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14440 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14440
    | exact resolve eq14440 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14440
  have eq14477 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (σ (τ X0)) (M.op X1 (M.op X2 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14405 X0 X1 X2
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq14405
    | exact resolve eq14405 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14405
  have eq14509 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14477 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14477
    | exact resolve eq14477 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14477
  have eq14566 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14509 (M.op X1 X0) X0 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq7690 (M.op X1 X0) X1 X0
       grind)
    | exact superpose eq7690 eq14509
    | exact resolve eq14509 eq7690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7690 eq14509
  have eq14873 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (k (σ (M.op X0 (τ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (M.op X0 (τ X1))
       have i₂ := eq14566 (τ X1) X0
       grind)
    | exact superpose eq14566 eq18
    | exact resolve eq18 eq14566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14566
  have eq34054 : ∀ X0 X1 X2 X3 : G, (k (τ X0) X1) = (M.op (τ X0) (k X1 (τ (M.op X2 (M.op X3 (σ (M.op X1 X1))))))) ∨ (τ X0) = (M.op (τ X0) (k X1 (τ (M.op X2 (M.op X3 (σ (M.op X1 X1))))))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (τ X0) (k X1 (τ (M.op X2 (M.op X3 (σ (M.op X1 X1))))))
       have i₂ := eq14460 X1 X0 X2 X3
       grind)
    | exact superpose eq14460 eq14
    | (have j0 := eq14 (τ X0) (k X1 (τ (M.op X2 (M.op X3 (σ (M.op X1 X1))))))
       grind)
    | exact resolve eq14 eq14460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14460
  have eq34057 : ∀ X0 X1 X2 X3 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) (k X1 (τ (M.op X2 (M.op X3 (σ (M.op X1 X1))))))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq34054 X0 X1 X2 X3
       have i₂ := eq14461 X1 X2 X3
       grind)
    | exact superpose eq14461 eq34054
    | (have j0 := eq34054 X0 X1 X2 X3
       grind)
    | exact resolve eq34054 eq14461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34054
  have eq34113 : ∀ X0 X1 X2 X3 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) (k X1 (τ (M.op X2 (M.op X3 (σ (M.op X1 X1))))))) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq34057 X0 X1 X2 X3
       have j1 := eq12 (τ X0) X1
       grind)
    | (have r₁ := eq34057 X0 X1 X2 X3
       have r₂ := eq12 (τ X0) X1
       grind)
    | exact resolve eq34057 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34057
  have eq34148 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34113 X0 X1 x x
       have i₂ := eq14461 X1 x x
       grind)
    | exact superpose eq14461 eq34113
    | (have j0 := eq34113 X0 X1 x x
       grind)
    | exact resolve eq34113 eq14461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14461 eq34113
  have eq34480 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34148 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq34148
    | exact resolve eq34148 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34148
  have eq35085 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (M.op (σ (M.op X0 (τ X1))) X1) ∨ (σ (M.op X0 (τ X1))) = (M.op (σ (M.op X0 (τ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14873 X0 X1
       have i₂ := eq34480 (σ (M.op X0 (τ X1))) X1
       grind)
    | exact superpose eq34480 eq14873
    | (have j1 := eq34480 (σ (M.op X0 (τ X1))) X1
       grind)
    | exact resolve eq14873 eq34480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14873
  have eq35150 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (M.op (σ (M.op X0 (τ X1))) X1) := by
    intro X0 X1
    first
    | (have j0 := eq35085 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35085
  have eq37671 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ (M.op X1 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35150 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq35150
    | exact resolve eq35150 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35150
  have eq92291 : ∀ X0 X1 X2 X3 : G, (σ (k X0 (τ X1))) = (k (σ X0) (M.op X2 (M.op X3 (σ (M.op X0 X0))))) ∨ (k (σ X0) (M.op X2 (M.op X3 (σ (M.op X0 X0))))) = (M.op (k (σ X0) (M.op X2 (M.op X3 (σ (M.op X0 X0))))) (k (σ X0) (M.op X2 (M.op X3 (σ (M.op X0 X0)))))) ∨ (σ (k X0 (τ X1))) = (M.op (k (σ X0) (M.op X2 (M.op X3 (σ (M.op X0 X0))))) (σ (τ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2001 X0 (M.op X1 (M.op X2 (σ (M.op X0 X0)))) (τ X3)
       have i₂ := eq14459 X0 X1 X2 X3
       grind)
    | exact superpose eq14459 eq2001
    | (have j0 := eq2001 X0 (M.op X2 (M.op X3 (σ (M.op X0 X0)))) X2
       grind)
    | exact resolve eq2001 eq14459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2001 eq14459
  have eq92697 : ∀ X0 X1 X2 X3 : G, (σ X0) = (σ (k X0 (τ X1))) ∨ (k (σ X0) (M.op X2 (M.op X3 (σ (M.op X0 X0))))) = (M.op (k (σ X0) (M.op X2 (M.op X3 (σ (M.op X0 X0))))) (k (σ X0) (M.op X2 (M.op X3 (σ (M.op X0 X0)))))) ∨ (σ (k X0 (τ X1))) = (M.op (k (σ X0) (M.op X2 (M.op X3 (σ (M.op X0 X0))))) (σ (τ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq92291 X0 X1 X2 X3
       have i₂ := eq14339 X0 X2 X3
       grind)
    | exact superpose eq14339 eq92291
    | (have j0 := eq92291 X0 X1 X2 X3
       grind)
    | exact resolve eq92291 eq14339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92291
  have eq92781 : ∀ X0 X1 X2 X3 : G, (σ X0) = (k (σ X0) X1) ∨ (k (σ X0) (M.op X2 (M.op X3 (σ (M.op X0 X0))))) = (M.op (k (σ X0) (M.op X2 (M.op X3 (σ (M.op X0 X0))))) (k (σ X0) (M.op X2 (M.op X3 (σ (M.op X0 X0)))))) ∨ (σ (k X0 (τ X1))) = (M.op (k (σ X0) (M.op X2 (M.op X3 (σ (M.op X0 X0))))) (σ (τ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq92697 X0 X1 X2 X3
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq92697
    | (have j0 := eq92697 X0 X1 X2 X3
       grind)
    | exact resolve eq92697 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92697
  have eq92860 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ (k X0 (τ X1))) = (M.op (k (σ X0) (M.op X2 (M.op X3 (σ (M.op X0 X0))))) (σ (τ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq92781 X0 X1 X1 X2
       have i₂ := eq14339 X0 X1 X2
       grind)
    | exact superpose eq14339 eq92781
    | (have j0 := eq92781 X0 X1 X2 X3
       grind)
    | exact resolve eq92781 eq14339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92781
  have eq92934 : ∀ X0 X1 X2 X3 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ (k X0 (τ X1))) = (M.op (k (σ X0) (M.op X2 (M.op X3 (σ (M.op X0 X0))))) (σ (τ X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq92860 X0 X1 X2 X3
       have i₂ := eq1156 X0
       grind)
    | exact superpose eq1156 eq92860
    | (have j0 := eq92860 X0 X1 X2 X3
       grind)
    | exact resolve eq92860 eq1156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156 eq92860
  have eq92998 : ∀ X0 X1 X2 X3 : G, (σ (k X0 (τ X1))) = (M.op (k (σ X0) (M.op X2 (M.op X3 (σ (M.op X0 X0))))) X1) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq92934 X0 X1 X2 X3
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq92934
    | (have j0 := eq92934 X0 X1 X2 X3
       grind)
    | exact resolve eq92934 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92934
  have eq93028 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op (σ X0) X1) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq92998 X0 X1 x x
       have i₂ := eq14339 X0 x x
       grind)
    | exact superpose eq14339 eq92998
    | (have j0 := eq92998 X0 X1 x x
       grind)
    | exact resolve eq92998 eq14339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14339 eq92998
  have eq93054 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq93028 X0 X1
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq93028
    | (have j0 := eq93028 X0 X1
       grind)
    | exact resolve eq93028 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq93028
  have eq93075 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq93054 X0 X1
       have j1 := eq1115 X0 X1
       grind)
    | (have r₁ := eq93054 X0 X1
       have r₂ := eq1115 X0 X1
       grind)
    | exact resolve eq93054 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115 eq93054
  have eq137137 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq93075 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq93075
    | exact resolve eq93075 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93075
  have eq137979 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 X1
       have i₂ := eq137137 X0 (σ X1)
       grind)
    | exact superpose eq137137 eq26
    | (have j1 := eq137137 X0 (σ X1)
       grind)
    | exact resolve eq26 eq137137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq137137
  have eq144590 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 (σ X1)
       have i₂ := eq137979 (σ X0) X1
       grind)
    | exact superpose eq137979 eq32
    | (have j1 := eq137979 (σ X0) X1
       grind)
    | exact resolve eq32 eq137979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq137979
  have eq144702 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq144590 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq144590
    | (have j0 := eq144590 X0 X1
       grind)
    | exact resolve eq144590 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144590
  have eq144787 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq144702 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq144702
    | (have j0 := eq144702 X0 X1
       grind)
    | exact resolve eq144702 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144702
  have eq144833 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq144787 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq144787
    | (have j0 := eq144787 X0 X1
       grind)
    | exact resolve eq144787 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144787
  have eq145973 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq144833 X0 X1
       grind)
    | exact superpose eq144833 eq11
    | (have j1 := eq144833 X0 X1
       grind)
    | exact resolve eq11 eq144833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144833
  have eq151063 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq145973 X0 X1
       have i₂ := eq34480 X0 X1
       grind)
    | exact superpose eq34480 eq145973
    | (have j1 := eq34480 X0 X1
       grind)
    | exact resolve eq145973 eq34480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34480 eq145973
  have eq151304 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq151063 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151063
  have eq153212 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq151304 x y
       grind)
    | exact superpose eq151304 eq16
    | (have j1 := eq151304 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq151304 x y
       grind)
    | exact resolve eq16 eq151304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151304
  have eq153742 : x = (M.op x y) := by grind
  clear eq153212
  have eq154181 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37671 y x
       have i₂ := eq153742
       grind)
    | exact superpose eq153742 eq37671
    | exact resolve eq37671 eq153742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37671
  have eq154939 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq154181
       grind)
    | exact superpose eq154181 eq16
    | exact resolve eq16 eq154181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154181
  have eq155144 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq154939
       have i₂ := eq153742
       grind)
    | exact superpose eq153742 eq154939
    | exact resolve eq154939 eq153742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153742 eq154939
  have eq155145 : False := by grind
  exact eq155145

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_y_pxy_y_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq284 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq284 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq287 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq285 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq285 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq285 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq298 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq287 (σ X0)
       grind)
    | exact superpose eq287 eq15
    | exact resolve eq15 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq298 X0
       have i₂ := eq287 X0
       grind)
    | exact superpose eq287 eq298
    | exact resolve eq298 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287 eq298
  have eq360 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq317 X0
       grind)
    | exact superpose eq317 eq14
    | (have j0 := eq14 (σ X0) X1
       grind)
    | exact resolve eq14 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq317 X0
       grind)
    | exact superpose eq317 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq367 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq360 X0 X1
       have j1 := eq362 X0 X1
       grind)
    | (have r₁ := eq360 X0 X1
       have r₂ := eq362 X0 X1
       grind)
    | exact resolve eq360 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360 eq362
  have eq482 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq367 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq367
    | exact resolve eq367 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq488 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq367 X0 (σ X1)
       grind)
    | exact superpose eq367 eq15
    | (have j1 := eq367 X0 (σ X1)
       grind)
    | exact resolve eq15 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq522 : ∀ X0 X1 : G, (τ X1) = (M.op X0 (τ X1)) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq482 X0 (τ X1)
       grind)
    | exact superpose eq482 eq18
    | (have j1 := eq482 X0 (τ X1)
       grind)
    | exact resolve eq18 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq533 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq482 (τ X0) X1
       grind)
    | exact superpose eq482 eq17
    | (have j1 := eq482 (τ X0) X1
       grind)
    | exact resolve eq17 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq482
  have eq754 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq533 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq533
    | exact resolve eq533 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq812 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq754 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq754
    | (have j0 := eq754 X0 X1
       grind)
    | exact resolve eq754 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq1278 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq522 X1 X0
       grind)
    | exact superpose eq522 eq13
    | (have j0 := eq13 X1 (τ X0)
       have j1 := eq522 X1 X0
       grind)
    | (have r₁ := eq13 X0 (τ X1)
       have r₂ := eq522 X0 X1
       grind)
    | exact resolve eq13 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq1283 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = (k X1 (τ X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1278 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278
  have eq1508 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq488 x y
       grind)
    | exact superpose eq488 eq16
    | (have j1 := eq488 x y
       grind)
    | exact resolve eq16 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1543 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq488 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq33059 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (τ X1) = (k X0 (τ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 (τ X1))
       have i₂ := eq1283 X1 X0
       grind)
    | exact superpose eq1283 eq10
    | (have j1 := eq1283 X1 X0
       grind)
    | exact resolve eq10 eq1283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283
  have eq33129 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (τ X1) = (k X0 (τ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq33059 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq33059
    | (have j0 := eq33059 X0 X1
       grind)
    | exact resolve eq33059 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq33059
  have eq33171 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (τ X1) = (k X0 (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq33129 X0 X1
       have j1 := eq12 X0 (τ X1)
       grind)
    | (have r₁ := eq33129 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq33129 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33129
  have eq33282 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq33171 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33171
    | exact resolve eq33171 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33171
  have eq33798 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1508
       have i₂ := eq33282 y x
       grind)
    | exact superpose eq33282 eq1508
    | (have j1 := eq33282 y x
       grind)
    | exact resolve eq1508 eq33282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1508
  have eq33799 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq33282 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33282
  have eq33800 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq33798
  have eq34004 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1543 x y
       have i₂ := eq33800
       grind)
    | exact superpose eq33800 eq1543
    | (have j0 := eq1543 x y
       grind)
    | exact resolve eq1543 eq33800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543 eq33800
  have eq34031 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq34004
  have eq34032 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq34031
  have eq34039 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34032
       grind)
    | exact superpose eq34032 eq16
    | exact resolve eq16 eq34032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34046 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq33799 (σ x) (σ y)
       have i₂ := eq34032
       grind)
    | exact superpose eq34032 eq33799
    | (have j0 := eq33799 (σ x) (σ y)
       grind)
    | (have r₁ := eq33799 (σ x) (σ y)
       have r₂ := eq34032
       grind)
    | exact resolve eq33799 eq34032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33799 eq34032
  have eq34047 : (σ y) = (k (σ x) (σ y)) := by grind
  clear eq34046
  have eq34049 : (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq34047
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq34047
    | exact resolve eq34047 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34047
  have eq34063 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq812 x y
       have i₂ := eq34049
       grind)
    | exact superpose eq34049 eq812
    | (have j0 := eq812 x y
       grind)
    | exact resolve eq812 eq34049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812 eq34049
  have eq34160 : y = (M.op x y) := by
    first
    | (have r₁ := eq34063
       have r₂ := eq34039
       grind)
    | exact resolve eq34063 eq34039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34063
  have eq34211 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq34039
       have i₂ := eq34160
       grind)
    | exact superpose eq34160 eq34039
    | exact resolve eq34039 eq34160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34039 eq34160
  have eq34223 : False := by grind
  exact eq34223

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyx_x_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X0 := by
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
  clear eq17
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq26
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq70 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq32
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq32 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq80 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
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
  have eq105 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq69 x y
       grind)
    | exact superpose eq69 eq16
    | (have j1 := eq69 x y
       grind)
    | exact resolve eq16 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq69 X0 X0
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq69 X0 X0
       grind)
    | (have r₁ := eq12 (σ X0) X1
       have r₂ := eq69 X0 X0
       grind)
    | (have r₁ := eq12 (σ X0) X1
       have r₂ := eq69 X0 X1
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq69 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq114 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq113 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq118 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq107 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq121 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq118 X0 X1
       have j1 := eq12 (σ X0) X1
       grind)
    | (have r₁ := eq118 X0 X1
       have r₂ := eq12 (σ X0) X1
       grind)
    | exact resolve eq118 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq627 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq80 x X2 X0 X1
       grind)
    | exact superpose eq80 eq9
    | exact resolve eq9 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq653 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq627 x X1 X0
       grind)
    | exact superpose eq627 eq9
    | exact resolve eq9 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq692 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq105
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq105
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq105 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq693 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq692
  have eq4505 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq70 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq4506 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq4505 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4505
  have eq4509 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4506 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4506
    | (have j0 := eq4506 X0
       grind)
    | exact resolve eq4506 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4506
  have eq4511 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4509 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4509
    | exact resolve eq4509 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4509
  have eq4573 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4511 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq4511
    | (have j0 := eq4511 X0
       grind)
    | exact resolve eq4511 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq4511
  have eq4591 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4573 X0
       grind)
    | exact superpose eq4573 eq11
    | (have j1 := eq4573 X0
       grind)
    | exact resolve eq11 eq4573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4573
  have eq4663 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4591 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4591
    | (have j0 := eq4591 X0
       grind)
    | exact resolve eq4591 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4591
  have eq4677 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4663 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq4663 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq4663 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4663
  have eq4753 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq114 X0
       have i₂ := eq4677 X0
       grind)
    | exact superpose eq4677 eq114
    | (have j0 := eq114 X0
       grind)
    | exact resolve eq114 eq4677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq4757 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq121 X0 X1
       have i₂ := eq4677 X0
       grind)
    | exact superpose eq4677 eq121
    | (have j0 := eq121 X0 X1
       grind)
    | exact resolve eq121 eq4677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq4792 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4677 (σ X0)
       grind)
    | exact superpose eq4677 eq15
    | exact resolve eq15 eq4677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4848 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4792 X0
       have i₂ := eq4677 X0
       grind)
    | exact superpose eq4677 eq4792
    | exact resolve eq4792 eq4677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4677 eq4792
  have eq5253 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq653 (σ X0) (σ X0)
       have i₂ := eq4848 X0
       grind)
    | exact superpose eq4848 eq653
    | exact resolve eq653 eq4848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7384 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq653 x y
       have i₂ := eq693
       grind)
    | exact superpose eq693 eq653
    | exact resolve eq653 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq7398 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq7384
  have eq7416 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq7398
       have i₂ := eq4848 x
       grind)
    | exact superpose eq4848 eq7398
    | exact resolve eq7398 eq4848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7398
  have eq13068 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq653 (σ x) (σ y)
       have i₂ := eq7416
       grind)
    | exact superpose eq7416 eq653
    | exact resolve eq653 eq7416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653 eq7416
  have eq13084 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq4753 x
       grind)
    | (have r₁ := eq13068
       have r₂ := eq4753 x
       grind)
    | exact resolve eq13068 eq4753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13068
  have eq13096 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13084
       have i₂ := eq4848 x
       grind)
    | exact superpose eq4848 eq13084
    | exact resolve eq13084 eq4848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13084
  have eq13124 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq4757 x X0
       have i₂ := eq13096
       grind)
    | exact superpose eq13096 eq4757
    | (have j0 := eq4757 x X0
       grind)
    | (have r₁ := eq4757 x x
       have r₂ := eq13096
       grind)
    | exact resolve eq4757 eq13096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13131 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5253 x
       have i₂ := eq13096
       grind)
    | exact superpose eq13096 eq5253
    | exact resolve eq5253 eq13096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5253 eq13096
  have eq13166 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq13124 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13124
  have eq13173 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq4753 x
       grind)
    | (have r₁ := eq13131
       have r₂ := eq4753 x
       grind)
    | exact resolve eq13131 eq4753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4753 eq13131
  have eq13176 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq13166 X0
       have j1 := eq4757 x X0
       grind)
    | (have r₁ := eq13166 X0
       have r₂ := eq4757 x x
       grind)
    | exact resolve eq13166 eq4757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4757 eq13166
  have eq13182 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13173
       have i₂ := eq4848 x
       grind)
    | exact superpose eq4848 eq13173
    | exact resolve eq13173 eq4848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4848 eq13173
  have eq13507 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq13182
       grind)
    | exact superpose eq13182 eq10
    | exact resolve eq10 eq13182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13182
  have eq13605 : x = (M.op x x) := by
    first
    | (have i₁ := eq13507
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq13507
    | exact resolve eq13507 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13507
  have eq13627 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x X0
       have i₂ := eq13605
       grind)
    | exact superpose eq13605 eq12
    | (have j0 := eq12 x X0
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq13605
       grind)
    | exact resolve eq12 eq13605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13605
  have eq13684 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq13627 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13627
  have eq14052 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq13176 (σ X0)
       grind)
    | exact superpose eq13176 eq15
    | exact resolve eq15 eq13176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13176
  have eq14122 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq14052 X0
       have i₂ := eq13684 X0
       grind)
    | exact superpose eq13684 eq14052
    | exact resolve eq14052 eq13684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13684 eq14052
  have eq15090 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14122 y
       grind)
    | exact superpose eq14122 eq16
    | (have r₁ := eq16
       have r₂ := eq14122 y
       grind)
    | exact resolve eq16 eq14122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14122
  have eq15176 : False := by grind
  exact eq15176

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_x_y_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = X0 := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq66 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq71 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq80 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq71 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq81 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq80 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq96 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq81 (σ X0)
       grind)
    | exact superpose eq81 eq15
    | exact resolve eq15 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq81 (τ X0)
       grind)
    | exact superpose eq81 eq32
    | exact resolve eq32 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq105 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq98 X0
       have i₂ := eq81 X0
       grind)
    | exact superpose eq81 eq98
    | exact resolve eq98 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq107 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq96 X0
       have i₂ := eq81 X0
       grind)
    | exact superpose eq81 eq96
    | exact resolve eq96 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq96
  have eq204 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq213 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq204 X0 X1
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq204
    | (have j0 := eq204 X0 X1
       grind)
    | exact resolve eq204 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq630 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X0 X0))) ∨ (σ (k (τ X0) X1)) = (M.op (σ (τ X0)) (σ X1)) ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq213 (τ X0) X1
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq213
    | (have j0 := eq213 (τ X0) X1
       grind)
    | exact resolve eq213 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq213
  have eq677 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X0)) ∨ (σ (k (τ X0) X1)) = (M.op (σ (τ X0)) (σ X1)) ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq630 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq630
    | (have j0 := eq630 X0 X1
       grind)
    | exact resolve eq630 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq679 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k (τ X0) X1)) = (M.op (σ (τ X0)) (σ X1)) ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq677 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq677
    | (have j0 := eq677 X0 X1
       grind)
    | exact resolve eq677 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq680 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq679 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq679
    | (have j0 := eq679 X0 X1
       grind)
    | exact resolve eq679 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq681 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq680 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq680
    | (have j0 := eq680 X0 X1
       grind)
    | exact resolve eq680 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq680
  have eq682 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq681 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq681 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq681 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq683 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq682 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq682
    | (have j0 := eq682 X0 X1
       grind)
    | exact resolve eq682 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq684 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq683 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq683
    | exact resolve eq683 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq683 (σ X0) X1
       grind)
    | exact superpose eq683 eq15
    | (have j1 := eq683 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq725 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq684 (τ X1) X0
       grind)
    | exact superpose eq684 eq19
    | (have j1 := eq684 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq684
  have eq804 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq725 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq725
    | exact resolve eq725 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq849 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq804 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq804
    | (have j0 := eq804 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq804 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq1023 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq696 x y
       grind)
    | exact superpose eq696 eq16
    | (have j1 := eq696 x y
       grind)
    | exact resolve eq16 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq1040 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1023
       have i₂ := eq849 y x
       grind)
    | exact superpose eq849 eq1023
    | (have j1 := eq849 (σ x) (σ y)
       grind)
    | (have r₁ := eq1023
       have r₂ := eq849 y x
       grind)
    | (have r₁ := eq1023
       have r₂ := eq849 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1023
       have r₂ := eq849 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1023 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849 eq1023
  have eq1041 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1040
  have eq1044 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1041
       grind)
    | exact superpose eq1041 eq16
    | exact resolve eq16 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq1045 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1044
       have r₂ := eq107 x
       grind)
    | exact resolve eq1044 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1046 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1045
       grind)
    | exact superpose eq1045 eq16
    | exact resolve eq16 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1047 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1045
       grind)
    | exact superpose eq1045 eq10
    | exact resolve eq10 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1090 : x = y := by
    first
    | (have i₁ := eq1047
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1047
    | exact resolve eq1047 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047
  have eq1091 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1046
       have i₂ := eq107 x
       grind)
    | exact superpose eq107 eq1046
    | exact resolve eq1046 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq1046
  have eq1092 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1091
       have i₂ := eq1090
       grind)
    | exact superpose eq1090 eq1091
    | exact resolve eq1091 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090 eq1091
  have eq1093 : False := by grind
  exact eq1093

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_x_pxy_x_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
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
  have eq26 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq45 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 ∨ (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       grind)
    | (have r₁ := eq13 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 (M.op X0 X0) X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq13
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq21 X0
       grind)
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq46 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq48 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 ∨ (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq45 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq79 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
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
  have eq113 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op X2 (M.op (τ X0) (τ X0)))))) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (M.op X2 (M.op (τ X0) (τ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (M.op X1 (M.op X2 (M.op (τ X0) (τ X0))))
       have i₂ := eq48 (τ X0) X1 X2
       grind)
    | exact superpose eq48 eq18
    | (have j1 := eq48 (τ X0) X1 X2
       grind)
    | exact resolve eq18 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq117 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X2 (M.op (τ X0) (τ X0)))))) = X0 ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (M.op X2 (M.op (τ X0) (τ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq113 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq113
    | (have j0 := eq113 X0 X1 X2
       grind)
    | exact resolve eq113 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq122 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (M.op X0 (σ X1)) (σ X2)) ∨ (M.op X0 (σ X1)) = X0 ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X0 X1 X2
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq26
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq26 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq170 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq74 x y
       grind)
    | exact superpose eq74 eq16
    | (have j1 := eq74 x y
       grind)
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  clear eq47
  have eq308 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq302 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq302
    | (have j0 := eq302 X0
       grind)
    | exact resolve eq302 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq302
  have eq309 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq308 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq318 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq27 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq309 (σ X0)
       grind)
    | exact superpose eq309 eq27
    | exact resolve eq27 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq447 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79
    | exact resolve eq79 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq479 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq447 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq447
    | (have j0 := eq447 X0 X1
       grind)
    | exact resolve eq447 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq600 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq318 x
       have i₂ := eq74 x x
       grind)
    | exact superpose eq74 eq318
    | (have j1 := eq74 X0 X0
       grind)
    | exact resolve eq318 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq318
  have eq616 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq600 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq625 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq616 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq616
    | (have j0 := eq616 X0
       grind)
    | exact resolve eq616 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq1042 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq85 x X2 X0 X1
       grind)
    | exact superpose eq85 eq9
    | exact resolve eq9 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq1072 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) ∨ (M.op (M.op X1 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq48 (M.op X1 x) x X0
       have i₂ := eq1042 X0 X1 x
       grind)
    | exact superpose eq1042 eq48
    | exact resolve eq48 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq1077 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X2 X0
       have i₂ := eq1042 (M.op (M.op X1 X0) (M.op X1 X0)) X1 X0
       grind)
    | exact superpose eq1042 eq9
    | exact resolve eq9 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1113 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq170
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq170
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq170 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq1114 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq1113
  have eq1423 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) (σ (M.op X1 (M.op X2 (M.op X0 X0))))) ∨ (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq117 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq117
    | exact resolve eq117 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq1485 : ∀ X0 X1 X2 : G, (σ X0) = (σ (k X0 (M.op X1 (M.op X2 (M.op X0 X0))))) ∨ (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1423 X0 X1 X2
       have i₂ := eq15 X0 (M.op X1 (M.op X2 (M.op X0 X0)))
       grind)
    | exact superpose eq15 eq1423
    | (have j0 := eq1423 X0 X1 X2
       grind)
    | exact resolve eq1423 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1423
  have eq4331 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1042 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) X1 X2
       have i₂ := eq1077 (M.op X1 X2) X0 (M.op X1 X2)
       grind)
    | exact superpose eq1077 eq1042
    | exact resolve eq1042 eq1077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042 eq1077
  have eq11288 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (σ (k (M.op X1 X0) X0)) ∨ (M.op (M.op X1 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1485 (M.op X1 x) x (M.op (M.op X1 x) (M.op X1 x))
       have i₂ := eq4331 (M.op X1 x) X1 x
       grind)
    | exact superpose eq4331 eq1485
    | exact resolve eq1485 eq4331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1485 eq4331
  have eq14208 : (σ x) = (σ (k x y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11288 y x
       have i₂ := eq1114
       grind)
    | exact superpose eq1114 eq11288
    | exact resolve eq11288 eq1114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114 eq11288
  have eq14277 : (σ x) = (σ (k x y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14208
  have eq14302 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq178 x y
       grind)
    | (have r₁ := eq14277
       have r₂ := eq178 x y
       grind)
    | exact resolve eq14277 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq14277
  have eq14387 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k (τ (σ X0)) X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq309 (σ X0)
       have i₂ := eq122 (σ X0) X0 X0
       grind)
    | exact superpose eq122 eq309
    | (have j1 := eq122 (σ X0) X0 x
       grind)
    | exact resolve eq309 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq309
  have eq14402 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k (τ (σ X0)) X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq14387 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14387
  have eq14423 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14402 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14402
    | (have j0 := eq14402 X0
       grind)
    | exact resolve eq14402 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14402
  have eq14478 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14423 X0
       have i₂ := eq625 X0
       grind)
    | exact superpose eq625 eq14423
    | (have j0 := eq14423 X0
       have j1 := eq625 X0
       grind)
    | exact resolve eq14423 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625 eq14423
  have eq14559 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq14478 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14478
  have eq16434 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq14559
  have eq16481 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16434 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq16434
    | (have j0 := eq16434 X0
       grind)
    | exact resolve eq16434 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16434
  have eq16482 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq16481 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16481
  have eq16648 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq16482 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16482
    | exact resolve eq16482 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16702 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) := by
    intro X0
    grind
  have eq16775 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq16702 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq16702
    | exact resolve eq16702 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16702
  have eq16798 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq16648 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq16648
    | exact resolve eq16648 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq16648
  have eq16815 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq16798 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16798
    | exact resolve eq16798 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16798
  have eq21651 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq16775 X0
       have i₂ := eq16815 X0
       grind)
    | exact superpose eq16815 eq16775
    | exact resolve eq16775 eq16815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16775
  have eq21762 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq21651
  have eq138391 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14302
       grind)
    | exact superpose eq14302 eq16
    | exact resolve eq16 eq14302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138414 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1072 (σ y) (σ x)
       have i₂ := eq14302
       grind)
    | exact superpose eq14302 eq1072
    | exact resolve eq1072 eq14302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072 eq14302
  have eq138438 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq138414
  have eq138463 : (σ x) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq138438
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq138438
    | exact resolve eq138438 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138438
  have eq138485 : (σ y) = (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq138391
       have i₂ := eq16482 x
       grind)
    | exact superpose eq16482 eq138391
    | exact resolve eq138391 eq16482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138391
  have eq138508 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq138463
       have i₂ := eq16482 x
       grind)
    | exact superpose eq16482 eq138463
    | exact resolve eq138463 eq16482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16482 eq138463
  have eq138530 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq138485
       have i₂ := eq16815 x
       grind)
    | exact superpose eq16815 eq138485
    | exact resolve eq138485 eq16815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138485
  have eq138541 : y = (M.op x x) ∨ (σ x) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq138508
       have i₂ := eq16815 x
       grind)
    | exact superpose eq16815 eq138508
    | exact resolve eq138508 eq16815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16815 eq138508
  have eq139869 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq21762 x
       have i₂ := eq138541
       grind)
    | exact superpose eq138541 eq21762
    | exact resolve eq21762 eq138541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138541
  have eq139941 : (σ x) = (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq139869
       have r₂ := eq16
       grind)
    | exact resolve eq139869 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139869
  have eq139962 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq479 y x
       have i₂ := eq139941
       grind)
    | exact superpose eq139941 eq479
    | (have j0 := eq479 y x
       grind)
    | exact resolve eq479 eq139941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479 eq139941
  have eq140175 : x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq139962
       have r₂ := eq138530
       grind)
    | exact resolve eq139962 eq138530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139962
  have eq144150 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq138530
       have i₂ := eq140175
       grind)
    | exact superpose eq140175 eq138530
    | exact resolve eq138530 eq140175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138530 eq140175
  have eq144191 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq144150
  have eq144192 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq144191
  have eq144271 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq21762 x
       have i₂ := eq144192
       grind)
    | exact superpose eq144192 eq21762
    | exact resolve eq21762 eq144192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144192
  have eq144343 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq144271
       have r₂ := eq16
       grind)
    | exact resolve eq144271 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144271
  have eq145458 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq144343
       grind)
    | exact superpose eq144343 eq10
    | exact resolve eq10 eq144343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144343
  have eq145674 : y = (M.op x x) := by
    first
    | (have i₁ := eq145458
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq145458
    | exact resolve eq145458 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145458
  have eq145889 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21762 x
       have i₂ := eq145674
       grind)
    | exact superpose eq145674 eq21762
    | exact resolve eq21762 eq145674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21762 eq145674
  have eq145961 : False := by grind
  exact eq145961
