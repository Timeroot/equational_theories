import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation947`: `x = y ◇ ((z ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_pyy_pyy_pyx_pxy_Equation947 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law947 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law947.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op X0 (M.op (M.op x y) (M.op X0 y))) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X1 X2))) = X2 ∨ (M.op X2 X0) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 X0
       have i₂ := eq11 X2 X0
       grind)
    | (have i₁ := eq14 X1 X1 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq14
    | (have j1 := eq11 X2 X0
       grind)
    | exact resolve eq14 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 X0) (M.op X0 X1))) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X0 X2
       have i₂ := eq11 X1 X0
       grind)
    | (have i₁ := eq14 X0 X1 X2
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq14
    | (have j1 := eq11 X1 X0
       grind)
    | exact resolve eq14 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq11 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq110 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq116 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq115 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq113 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq113 x
       have r₂ := eq13 x x
       grind)
    | exact resolve eq113 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq118 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq116 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq116 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq116 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq123 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq117 sF2
       grind)
    | exact superpose eq117 eq49
    | exact resolve eq49 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq124 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq123
       have i₂ := eq117 x
       grind)
    | exact superpose eq117 eq123
    | exact resolve eq123 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq123
  have eq249 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq266 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ x)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq283 : ∀ X0 X1 : G, (M.op (M.op X1 y) (M.op x y)) = (M.op x (M.op (M.op X0 (M.op (M.op X1 y) (M.op x y))) y)) := by
    intro X0 X1
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq990 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X2 X2 X1
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1330 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X0 X1
       have i₂ := eq89 X0 X1 X0
       grind)
    | exact superpose eq89 eq83
    | (have j0 := eq83 X0 X1 X1
       have j1 := eq89 X0 X1 x
       grind)
    | exact resolve eq83 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq89
  have eq1347 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1330 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330
  have eq2394 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq990 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq990
    | (have j0 := eq990 y x X0
       grind)
    | exact resolve eq990 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2397 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op X0 (M.op (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq990
    | (have j0 := eq990 (σ y) (σ x) X0
       grind)
    | exact resolve eq990 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2414 : ∀ X0 : G, (M.op (M.op X0 y) (M.op x y)) = (M.op x (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq990 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq990
    | (have j0 := eq990 y X0 x
       grind)
    | exact resolve eq990 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2427 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 x
       have i₂ := eq990 X1 x X0
       grind)
    | exact superpose eq990 eq14
    | exact resolve eq14 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2565 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2427 (M.op X1 X0) X0
       have i₂ := eq990 X0 X1 X0
       grind)
    | exact superpose eq990 eq2427
    | exact resolve eq2427 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2605 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op X1 (M.op X0 X0)) X1
       have i₂ := eq2427 (M.op X1 (M.op X0 X0)) X0
       grind)
    | exact superpose eq2427 eq14
    | exact resolve eq14 eq2427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2690 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op y y)) := by
    first
    | (have i₁ := eq2394 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2394
    | (have j0 := eq2394 x
       grind)
    | exact resolve eq2394 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2394
  have eq2950 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq26 eq2397
    | (have j0 := eq2397 (σ x)
       grind)
    | exact resolve eq2397 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2397
  have eq3259 : ∀ X0 : G, (M.op (M.op X0 y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2414 X0
       have i₂ := eq2690
       grind)
    | exact superpose eq2690 eq2414
    | exact resolve eq2414 eq2690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2414
  have eq3651 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq249 eq2565
    | exact resolve eq2565 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3657 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq266 eq2565
    | exact resolve eq2565 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2565
  have eq3723 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3657
       have i₂ := eq2427 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq2427 eq3657
    | exact resolve eq3657 eq2427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3657
  have eq3728 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq3651
       have i₂ := eq2427 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq2427 eq3651
    | exact resolve eq3651 eq2427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2427 eq3651
  have eq3917 : y = (M.op x (M.op y (M.op x y))) := by
    first
    | exact superpose eq3728 eq249
    | exact resolve eq249 eq3728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7743 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq1347 y x
       grind)
    | exact superpose eq1347 eq44
    | (have j1 := eq1347 y x
       grind)
    | exact resolve eq44 eq1347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7825 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq7743
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7743
    | exact resolve eq7743 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7743
  have eq7867 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq7825
    | exact resolve eq7825 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7825
  have eq7897 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq7867
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7867
    | exact resolve eq7867 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7867
  have eq8041 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7897 eq1347
    | (have j0 := eq1347 (σ y) (σ x)
       grind)
    | exact resolve eq1347 eq7897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8043 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7897 eq118
    | exact resolve eq118 eq7897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq7897
  have eq8044 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq8043
    | exact resolve eq8043 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8043
  have eq8046 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq8041
    | exact resolve eq8041 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8041
  have eq8051 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq8044
       have r₂ := eq27
       grind)
    | exact resolve eq8044 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8044
  have eq8053 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq8046
       have r₂ := eq27
       grind)
    | exact resolve eq8046 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8046
  have eq8058 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq8053
    | exact resolve eq8053 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8053
  have eq8307 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq8058 eq27
    | exact resolve eq27 eq8058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8311 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq8058 eq266
    | exact resolve eq266 eq8058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq8326 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2950 eq8311
    | exact resolve eq8311 eq2950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2950 eq8311
  have eq8329 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq3723 eq8326
    | exact resolve eq8326 eq3723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3723 eq8326
  have eq9380 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op x (M.op (M.op X0 (M.op (M.op x y) (M.op x y))) y)) := by
    intro X0
    first
    | exact superpose eq3259 eq283
    | (have j0 := eq283 X0 x
       grind)
    | exact resolve eq283 eq3259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283 eq3259
  have eq9381 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op x (M.op (M.op X0 (M.op y (M.op x y))) y)) := by
    intro X0
    first
    | exact superpose eq3728 eq9380
    | exact resolve eq9380 eq3728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9380
  have eq11514 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq8058 eq8329
    | exact resolve eq8329 eq8058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8058 eq8329
  have eq11563 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq11514
  have eq11745 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq11563 eq8051
    | exact resolve eq8051 eq11563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8051 eq11563
  have eq11797 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq11745
  have eq11819 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11797
       have r₂ := eq8307
       grind)
    | exact resolve eq11797 eq8307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8307 eq11797
  have eq11833 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq11819 eq29
    | exact resolve eq29 eq11819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11819
  have eq11923 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq11833
    | exact resolve eq11833 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11833
  have eq11924 : y = (M.op x y) ∨ x = y := by grind
  clear eq11923
  have eq11930 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq11924 eq20
    | exact resolve eq20 eq11924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11991 : y = (M.op x (M.op y y)) ∨ x = y := by
    first
    | exact superpose eq11924 eq3917
    | exact resolve eq3917 eq11924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12000 : ∀ X0 : G, (M.op y y) = (M.op x (M.op (M.op X0 (M.op y y)) y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq11924 eq9381
    | exact resolve eq9381 eq11924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9381
  have eq12003 : (M.op y y) = (M.op x (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq12000 x
       have i₂ := eq2605 y x
       grind)
    | exact superpose eq2605 eq12000
    | exact resolve eq12000 eq2605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2605 eq12000
  have eq12004 : y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq11991
       have i₂ := eq2690
       grind)
    | exact superpose eq2690 eq11991
    | exact resolve eq11991 eq2690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11991
  have eq12054 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11930
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11930
    | exact resolve eq11930 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11930
  have eq12055 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq12003
       have i₂ := eq2690
       grind)
    | exact superpose eq2690 eq12003
    | exact resolve eq12003 eq2690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12003
  have eq12056 : y = (M.op y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq3728 eq12004
    | exact resolve eq12004 eq3728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12004
  have eq12073 : (M.op y y) = (M.op y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq3728 eq12055
    | exact resolve eq12055 eq3728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12055
  have eq12182 : y = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq11924 eq12056
    | exact resolve eq12056 eq11924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11924 eq12056
  have eq12234 : y = (M.op y y) ∨ x = y := by grind
  clear eq12182
  have eq12331 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq2690
       have i₂ := eq12234
       grind)
    | exact superpose eq12234 eq2690
    | exact resolve eq2690 eq12234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12234
  have eq12406 : (M.op x y) = (M.op y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq3728 eq12331
    | exact resolve eq12331 eq3728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12331
  have eq12417 : (M.op x y) = (M.op y (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq12406
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12406
    | exact resolve eq12406 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12406
  have eq12599 : y = (M.op x (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq12417 eq3917
    | exact resolve eq3917 eq12417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3917
  have eq13953 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq12073 eq12417
    | exact resolve eq12417 eq12073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12417
  have eq13989 : (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq13953
  have eq14193 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq2690
       have i₂ := eq13989
       grind)
    | exact superpose eq13989 eq2690
    | exact resolve eq2690 eq13989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13989
  have eq14275 : (M.op x (M.op x y)) = (M.op y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq3728 eq14193
    | exact resolve eq14193 eq3728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14193
  have eq22028 : (M.op y y) = (M.op x (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq14275 eq12073
    | exact resolve eq12073 eq14275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12073
  have eq22082 : (M.op y y) = (M.op x (M.op x y)) ∨ x = y := by grind
  clear eq22028
  have eq25153 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq2690
       have i₂ := eq22082
       grind)
    | exact superpose eq22082 eq2690
    | exact resolve eq2690 eq22082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2690 eq22082
  have eq25262 : (M.op y (M.op x y)) = (M.op x (M.op x (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq3728 eq25153
    | exact resolve eq25153 eq3728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3728 eq25153
  have eq200909 : (M.op x (M.op x y)) ≠ (M.op y (M.op x y)) ∨ (k x (M.op x (M.op x y))) = (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq25262 eq13
    | (have j0 := eq13 x (M.op x (M.op x y))
       grind)
    | exact resolve eq13 eq25262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25262
  have eq201086 : (k x (M.op x (M.op x y))) = (M.op (M.op x (M.op x y)) (M.op x (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq200909
       have r₂ := eq14275
       grind)
    | exact resolve eq200909 eq14275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14275 eq200909
  have eq201118 : (M.op x (M.op (M.op x y) (M.op x y))) = (k x (M.op x (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq201086
       have i₂ := eq990 sF0 x x
       grind)
    | exact superpose eq990 eq201086
    | exact resolve eq201086 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990 eq201086
  have eq201128 : y = (k x (M.op x (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq249 eq201118
    | exact resolve eq201118 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq201118
  have eq202575 : y = (k x y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq12599 eq201128
    | exact resolve eq201128 eq12599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12599 eq201128
  have eq202591 : y = (k x y) ∨ x = y := by grind
  clear eq202575
  have eq202603 : (σ y) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq202591
       grind)
    | exact superpose eq202591 eq44
    | exact resolve eq44 eq202591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq202591
  have eq202641 : (σ y) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq202603
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq202603
    | exact resolve eq202603 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202603
  have eq202728 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq202641 eq1347
    | (have j0 := eq1347 (σ y) (σ x)
       grind)
    | exact resolve eq1347 eq202641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347 eq202641
  have eq202732 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq202728
  have eq202758 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq202732
    | exact resolve eq202732 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202732
  have eq205807 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq202758 eq27
    | exact resolve eq27 eq202758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202758
  have eq206204 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq205807
       have r₂ := eq12054
       grind)
    | exact resolve eq205807 eq12054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12054 eq205807
  have eq206227 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq206204 eq29
    | exact resolve eq29 eq206204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq206204
  have eq206908 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq206227
    | exact resolve eq206227 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq206227
  have eq206909 : x = y := by grind
  clear eq206908
  have eq206915 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq206909
       grind)
    | exact superpose eq206909 eq18
    | exact resolve eq18 eq206909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq206916 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq206909
       grind)
    | exact superpose eq206909 eq24
    | exact resolve eq24 eq206909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq206909
  have eq207086 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq206916
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq206916
    | exact resolve eq206916 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq206916
  have eq207125 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq207086 eq26
    | exact resolve eq26 eq207086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq207086
  have eq208724 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq207125 eq124
    | exact resolve eq124 eq207125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq207125
  have eq209028 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq208724
       have i₂ := eq206915
       grind)
    | exact superpose eq206915 eq208724
    | exact resolve eq208724 eq206915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206915 eq208724
  have eq209078 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq209028 eq15
    | exact resolve eq15 eq209028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209028
  have eq209129 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq209078
    | exact resolve eq209078 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq209078
  have eq209144 : False := by grind
  exact eq209144

/-- `Equation947`: `x = y ◇ ((z ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,Y) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pxx_x_pyx_Equation947 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law947 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law947.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op X0 (M.op (M.op x y) (M.op X0 y))) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X0) (M.op X1 X0))) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X0) (M.op X1 X0)) X1 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq68 sF2
       grind)
    | exact superpose eq68 eq49
    | exact resolve eq49 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq73 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq72
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq72
    | exact resolve eq72 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq72
  have eq100 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq100
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq100 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq109
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq109
    | exact resolve eq109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
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
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
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
  have eq238 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq245 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ x)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq561 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X3 (M.op (M.op X2 X0) (M.op X1 X0)))) = (M.op X4 (M.op (M.op (M.op X2 X0) (M.op X1 X0)) (M.op X4 (M.op X0 (M.op X3 (M.op (M.op X2 X0) (M.op X1 X0))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op (M.op X2 X0) (M.op X1 X0)) X1 X2 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq582 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X2 X2 X1
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq686 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op (M.op X4 (M.op (M.op X0 X1) (M.op X2 X1))) X1)) (M.op (M.op X0 X1) (M.op X2 X1))) = (M.op X5 (M.op (M.op (M.op X4 (M.op (M.op X0 X1) (M.op X2 X1))) X1) (M.op X5 (M.op (M.op X3 (M.op (M.op X4 (M.op (M.op X0 X1) (M.op X2 X1))) X1)) (M.op (M.op X0 X1) (M.op X2 X1)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op (M.op X2 (M.op (M.op X3 X0) (M.op X1 X0))) X0) X1 X1 X3
       have i₂ := eq55 X0 X1 X2 X3
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1092 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 x
       have i₂ := eq582 X1 x X0
       grind)
    | exact superpose eq582 eq14
    | exact resolve eq14 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1171 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1092 (M.op X1 X0) X0
       have i₂ := eq582 X0 X1 X0
       grind)
    | exact superpose eq582 eq1092
    | exact resolve eq1092 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1176 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 X1 X0 X0
       have i₂ := eq1092 X1 (M.op X0 X1)
       grind)
    | exact superpose eq1092 eq52
    | exact resolve eq52 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1189 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op X1 (M.op X0 X0)) X1
       have i₂ := eq1092 (M.op X1 (M.op X0 X0)) X0
       grind)
    | exact superpose eq1092 eq14
    | exact resolve eq14 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1195 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1176 X0 X1
       have i₂ := eq582 X1 X0 X0
       grind)
    | exact superpose eq582 eq1176
    | exact resolve eq1176 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176
  have eq1758 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq238 eq1171
    | exact resolve eq1171 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1764 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq245 eq1171
    | exact resolve eq1171 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1800 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1764
       have i₂ := eq1092 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq1092 eq1764
    | exact resolve eq1764 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1764
  have eq1805 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1758
       have i₂ := eq1092 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq1092 eq1758
    | exact resolve eq1758 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1758
  have eq1898 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1800 eq245
    | exact resolve eq245 eq1800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq1928 : y = (M.op x (M.op y (M.op x y))) := by
    first
    | exact superpose eq1805 eq238
    | exact resolve eq238 eq1805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq2675 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1805 eq1195
    | exact resolve eq1195 eq1805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1805
  have eq2676 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1800 eq1195
    | exact resolve eq1195 eq1800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800
  have eq2699 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1195 (M.op X1 X0) (M.op X0 (M.op X0 X0))
       have i₂ := eq1171 X0 X1
       grind)
    | exact superpose eq1171 eq1195
    | exact resolve eq1195 eq1171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2816 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X0) (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2699 X0 X1
       have i₂ := eq582 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq582 eq2699
    | exact resolve eq2699 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2699
  have eq2856 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2816 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq2816
    | exact resolve eq2816 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2816
  have eq2878 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2856 X0 X1
       have i₂ := eq1189 X0 X0
       grind)
    | exact superpose eq1189 eq2856
    | exact resolve eq2856 eq1189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2856
  have eq13234 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X3 (M.op X1 (M.op X0 X0)))) = (M.op X4 (M.op (M.op X1 (M.op X0 X0)) (M.op X4 (M.op X0 (M.op X3 (M.op X1 (M.op X0 X0))))))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq561 X0 x X1 X3 X4
       have i₂ := eq582 X0 X1 x
       grind)
    | exact superpose eq582 eq561
    | exact resolve eq561 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq13418 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) (M.op X1 X1)))) = (M.op X2 (M.op (M.op (M.op X0 X1) (M.op X1 X1)) (M.op (M.op X0 X1) (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13234 X1 (M.op X0 X1) X2 X2
       have i₂ := eq52 X1 X2 X1 X0
       grind)
    | exact superpose eq52 eq13234
    | exact resolve eq13234 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq13234
  have eq13469 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) (M.op X1 X1)))) = (M.op X2 (M.op (M.op X0 X1) (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13418 X0 X1 X2
       have i₂ := eq582 (M.op X1 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq582 eq13418
    | exact resolve eq13418 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13418
  have eq13508 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) (M.op X1 X1)))) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13469 X0 X1 X2
       have i₂ := eq582 X1 X1 X1
       grind)
    | exact superpose eq582 eq13469
    | exact resolve eq13469 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13469
  have eq13535 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X1 (M.op X2 (M.op (M.op X0 X1) (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13508 X0 X1 X2
       have i₂ := eq1171 X1 X0
       grind)
    | exact superpose eq1171 eq13508
    | exact resolve eq13508 eq1171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13508
  have eq13557 : ∀ X1 X2 : G, (M.op X2 X1) = (M.op X1 (M.op X2 (M.op X1 (M.op X1 X1)))) := by
    intro X1 X2
    first
    | (have i₁ := eq13535 x X1 X2
       have i₂ := eq582 X1 x X1
       grind)
    | exact superpose eq582 eq13535
    | exact resolve eq13535 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13535
  have eq34503 : ∀ X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op (M.op X4 (M.op X2 (M.op X1 X1))) X1)) (M.op X2 (M.op X1 X1))) = (M.op X5 (M.op (M.op (M.op X4 (M.op X2 (M.op X1 X1))) X1) (M.op X5 (M.op (M.op X3 (M.op (M.op X4 (M.op X2 (M.op X1 X1))) X1)) (M.op X2 (M.op X1 X1)))))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq686 X1 x X2 X3 X4 X5
       have i₂ := eq582 x X1 X2
       grind)
    | exact superpose eq582 eq686
    | exact resolve eq686 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq36281 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X2 (M.op (M.op X0 (M.op X0 X0)) X0)) (M.op X0 (M.op X0 X0)))) (M.op (M.op X0 (M.op X0 X0)) X0)) = (M.op X3 (M.op (M.op (M.op X2 (M.op (M.op X0 (M.op X0 X0)) X0)) (M.op X0 (M.op X0 X0))) (M.op X3 (M.op (M.op X1 (M.op (M.op X2 (M.op (M.op X0 (M.op X0 X0)) X0)) (M.op X0 (M.op X0 X0)))) (M.op (M.op X0 (M.op X0 X0)) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq34503 (M.op X1 (M.op X1 X1)) X1 X3 x x
       have i₂ := eq13557 X1 (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq13557 eq34503
    | exact resolve eq34503 eq13557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34503
  have eq36333 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) (M.op X0 X0)) = (M.op X3 (M.op (M.op (M.op X2 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) (M.op X3 (M.op (M.op X1 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) (M.op X0 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq36281 X0 X1 X2 X3
       have i₂ := eq1189 X0 X0
       grind)
    | exact superpose eq1189 eq36281
    | exact resolve eq36281 eq1189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189 eq36281
  have eq36412 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) X0)) = (M.op X3 (M.op (M.op (M.op X2 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) (M.op X3 (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq36333 X1 X1 X2 X3
       have i₂ := eq1195 (M.op X1 (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) X1
       grind)
    | exact superpose eq1195 eq36333
    | exact resolve eq36333 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195 eq36333
  have eq36453 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) X0)) = (M.op X3 (M.op (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) (M.op X3 (M.op X0 (M.op (M.op X1 (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) X0))))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq36412 x X1 X1 X3
       have i₂ := eq582 (M.op x x) X1 x
       grind)
    | exact superpose eq582 eq36412
    | exact resolve eq36412 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq36412
  have eq36465 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X3 (M.op X0 (M.op X3 (M.op X0 (M.op (M.op X1 X0) X0))))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq36453 X0 X1 X3
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq36453
    | exact resolve eq36453 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36453
  have eq36471 : ∀ X0 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op X3 (M.op X0 (M.op X3 (M.op X0 (M.op X0 X0))))) := by
    intro X0 X3
    first
    | (have i₁ := eq36465 X0 x X3
       have i₂ := eq2878 X0 x
       grind)
    | exact superpose eq2878 eq36465
    | exact resolve eq36465 eq2878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2878 eq36465
  have eq36475 : ∀ X0 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op X3 (M.op X3 X0)) := by
    intro X0 X3
    first
    | (have i₁ := eq36471 X0 X3
       have i₂ := eq13557 X0 X3
       grind)
    | exact superpose eq13557 eq36471
    | exact resolve eq36471 eq13557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13557 eq36471
  have eq36589 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1092 X1 X1
       have i₂ := eq36475 X1 X0
       grind)
    | (have i₁ := eq1092 X0 X0
       have i₂ := eq36475 X0 X0
       grind)
    | exact superpose eq36475 eq1092
    | exact resolve eq1092 eq36475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092 eq36475
  have eq52451 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq118 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq52452 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq52451
    | exact resolve eq52451 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52451
  have eq52463 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq52452
       have r₂ := eq27
       grind)
    | exact resolve eq52452 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52452
  have eq52467 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq52463
    | exact resolve eq52463 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52463
  have eq52471 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq52467
    | exact resolve eq52467 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52467
  have eq52494 : (σ x) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq52471 eq36589
    | exact resolve eq36589 eq52471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52471
  have eq52496 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1898 eq52494
    | exact resolve eq52494 eq1898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52494
  have eq52566 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq52496 eq1171
    | exact resolve eq1171 eq52496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52496
  have eq52579 : (σ x) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq2676 eq52566
    | exact resolve eq52566 eq2676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2676 eq52566
  have eq52592 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1898 eq52579
    | exact resolve eq52579 eq1898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1898 eq52579
  have eq52593 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq52592
  have eq52622 : x = (M.op x (M.op y (M.op x y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq36589 y x
       have i₂ := eq52593
       grind)
    | exact superpose eq52593 eq36589
    | exact resolve eq36589 eq52593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36589 eq52593
  have eq52624 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1928 eq52622
    | exact resolve eq52622 eq1928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52622
  have eq53081 : x = (M.op (M.op x y) (M.op x (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1171 x x
       have i₂ := eq52624
       grind)
    | exact superpose eq52624 eq1171
    | exact resolve eq1171 eq52624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171 eq52624
  have eq53094 : x = (M.op x (M.op y (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2675 eq53081
    | exact resolve eq53081 eq2675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2675 eq53081
  have eq53118 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1928 eq53094
    | exact resolve eq53094 eq1928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1928 eq53094
  have eq53119 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq53118
  have eq53135 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq53119 eq29
    | exact resolve eq29 eq53119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq53119
  have eq53344 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq53135
    | exact resolve eq53135 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq53135
  have eq53345 : x = y := by grind
  clear eq53344
  have eq53372 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq53345
       grind)
    | exact superpose eq53345 eq18
    | exact resolve eq18 eq53345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq53373 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq53345
       grind)
    | exact superpose eq53345 eq24
    | exact resolve eq24 eq53345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq53345
  have eq53590 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq53373
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq53373
    | exact resolve eq53373 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq53373
  have eq54020 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq53590 eq26
    | exact resolve eq26 eq53590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq53590
  have eq55057 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq54020 eq73
    | exact resolve eq73 eq54020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq54020
  have eq55154 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq55057
       have i₂ := eq53372
       grind)
    | exact superpose eq53372 eq55057
    | exact resolve eq55057 eq53372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53372 eq55057
  have eq55184 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55154 eq15
    | exact resolve eq15 eq55154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55154
  have eq55274 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq55184
    | exact resolve eq55184 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq55184
  have eq55306 : False := by grind
  exact eq55306
