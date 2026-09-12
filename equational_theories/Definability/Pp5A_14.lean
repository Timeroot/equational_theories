import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pyx_pxx_pxy_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  clear eq43
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
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
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X1)) X3
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
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
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
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq78
    | exact resolve eq78 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq83
    | exact resolve eq83 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
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
  have eq97 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq105 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq105 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq105 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq110 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq106 y
       grind)
    | exact superpose eq106 eq70
    | exact resolve eq70 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq111 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq106 sF2
       grind)
    | exact superpose eq106 eq49
    | exact resolve eq49 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq112 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq111
       have i₂ := eq106 x
       grind)
    | exact superpose eq106 eq111
    | exact resolve eq111 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq113 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq110
       have i₂ := eq106 sF3
       grind)
    | exact superpose eq106 eq110
    | exact resolve eq110 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq119 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq97
       have i₂ := eq106 sF3
       grind)
    | exact superpose eq106 eq97
    | exact resolve eq97 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq120 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq119
       have i₂ := eq106 y
       grind)
    | exact superpose eq106 eq119
    | exact resolve eq119 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq119
  have eq129 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq433 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op y (M.op x y))))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X1) x X1 X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq455 : ∀ X0 : G, x = (M.op y (M.op X0 (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq456 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op (M.op X4 (M.op X2 X4)) (M.op (M.op X0 (M.op X1 X2)) X0))) X3) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X1 X3 (M.op X4 (M.op X2 X4))
       have i₂ := eq52 X2 X0 X1 X4
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op X1 (M.op X2 X1)) (M.op X0 (σ x)))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X2 (M.op (M.op (M.op X3 (M.op X0 X3)) (M.op X4 (M.op X1 X4))) X2))) = (M.op (M.op X5 X0) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op (M.op X3 (M.op X0 X3)) (M.op X4 (M.op X1 X4))) X5 X1 X2
       have i₂ := eq53 X1 X3 X0 X4
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1046 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq453 X2 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq453
    | exact resolve eq453 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1049 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X0 (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq453
    | exact resolve eq453 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1143 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq1049 eq453
    | exact resolve eq453 eq1049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq1222 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq1143 eq14
    | exact resolve eq14 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq1329 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x)))) = X0 := by
    intro X0
    first
    | exact superpose eq1222 eq453
    | exact resolve eq453 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1222
  have eq1499 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y X0)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1046 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1046
    | (have j0 := eq1046 y X0 x
       grind)
    | exact resolve eq1046 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1523 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq1329 (M.op x (M.op sF2 x))
       have i₂ := eq1046 sF2 x sF4
       grind)
    | exact superpose eq1046 eq1329
    | exact resolve eq1329 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046 eq1329
  have eq2026 : x = (M.op y (M.op (M.op (σ x) (M.op x y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq1523 eq455
    | exact resolve eq455 eq1523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq2029 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq1523 eq456
    | exact resolve eq456 eq1523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456 eq1523
  have eq9302 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq433 (M.op X1 (M.op x X1)) sF0 y
       have i₂ := eq53 y X1 x sF0
       grind)
    | exact superpose eq53 eq433
    | exact resolve eq433 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq433
  have eq20521 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (M.op X1 X0)) (M.op (σ y) (M.op (σ x) (σ y))))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq509 eq461
    | exact resolve eq461 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461 eq509
  have eq130201 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq86 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq130202 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq130201
    | exact resolve eq130201 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130201
  have eq130213 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq130202
       have r₂ := eq27
       grind)
    | exact resolve eq130202 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130202
  have eq130217 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq130213
    | exact resolve eq130213 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130213
  have eq130355 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq130217 eq20521
    | exact resolve eq20521 eq130217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130217
  have eq130362 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2029 eq130355
    | exact resolve eq130355 eq2029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2029 eq130355
  have eq130402 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq130362 eq120
    | exact resolve eq120 eq130362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq130362
  have eq130573 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq130402
    | exact resolve eq130402 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130402
  have eq130574 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq130573
  have eq130980 : y = (M.op y (M.op (M.op (σ x) (M.op x y)) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq20521 y y
       have i₂ := eq130574
       grind)
    | exact superpose eq130574 eq20521
    | exact resolve eq20521 eq130574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20521 eq130574
  have eq130989 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2026 eq130980
    | exact resolve eq130980 eq2026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2026 eq130980
  have eq131049 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq113
       have i₂ := eq130989
       grind)
    | exact superpose eq130989 eq113
    | exact resolve eq113 eq130989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq131063 : x = (M.op (M.op y y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1499 y
       have i₂ := eq130989
       grind)
    | exact superpose eq130989 eq1499
    | exact resolve eq1499 eq130989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499
  have eq131065 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq130989
       grind)
    | exact superpose eq130989 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq130989
       grind)
    | exact resolve eq13 eq130989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131183 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq131065 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131065
  have eq131221 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq131049
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq131049
    | exact resolve eq131049 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131049
  have eq131513 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq131221 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq131221
       grind)
    | exact resolve eq13 eq131221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131221
  have eq131632 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq131513 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131513
  have eq132179 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq131063
       have i₂ := eq130989
       grind)
    | exact superpose eq130989 eq131063
    | exact resolve eq131063 eq130989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130989 eq131063
  have eq132317 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq132179
  have eq132515 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) X3) = (M.op y (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X1)) (M.op (M.op x y) x)) X0))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq132317 eq521
    | exact resolve eq521 eq132317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq132582 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X2) X3) = (M.op y (M.op X0 (M.op (M.op X2 y) X0))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X2 X3
    first
    | exact superpose eq9302 eq132515
    | exact resolve eq132515 eq9302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9302 eq132515
  have eq132662 : ∀ X2 X3 : G, (M.op (M.op X3 X2) X3) = X2 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X2 X3
    first
    | (have i₁ := eq132582 x X2 X3
       have i₂ := eq453 X2 y x
       grind)
    | exact superpose eq453 eq132582
    | exact resolve eq132582 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453 eq132582
  have eq135391 : (σ (M.op y (M.op x y))) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq129
       have i₂ := eq131183 sF0
       grind)
    | exact superpose eq131183 eq129
    | exact resolve eq129 eq131183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq131183
  have eq227375 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq132317 eq135391
    | exact resolve eq135391 eq132317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132317 eq135391
  have eq227472 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq227375
  have eq227479 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq227472
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq227472
    | exact resolve eq227472 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227472
  have eq227492 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq227479 eq131632
    | exact resolve eq131632 eq227479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131632 eq227479
  have eq227495 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq227492
  have eq227674 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq227495 eq132662
    | exact resolve eq132662 eq227495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132662 eq227495
  have eq227675 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq227674
  have eq227677 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq227675
    | exact resolve eq227675 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227675
  have eq227750 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq227677
       have r₂ := eq27
       grind)
    | exact resolve eq227677 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227677
  have eq227759 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq227750 eq29
    | exact resolve eq29 eq227750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq227750
  have eq227999 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq227759
    | exact resolve eq227759 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq227759
  have eq228000 : x = y := by grind
  clear eq227999
  have eq228022 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq228000
       grind)
    | exact superpose eq228000 eq18
    | exact resolve eq18 eq228000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq228023 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq228000
       grind)
    | exact superpose eq228000 eq24
    | exact resolve eq24 eq228000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq228000
  have eq228265 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq228023
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq228023
    | exact resolve eq228023 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq228023
  have eq228298 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq228265 eq26
    | exact resolve eq26 eq228265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq228265
  have eq229100 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq228298 eq112
    | exact resolve eq112 eq228298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq228298
  have eq229448 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq229100
       have i₂ := eq228022
       grind)
    | exact superpose eq228022 eq229100
    | exact resolve eq229100 eq228022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228022 eq229100
  have eq229564 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq229448 eq15
    | exact resolve eq15 eq229448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229448
  have eq229646 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq229564
    | exact resolve eq229564 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq229564
  have eq229667 : False := by grind
  exact eq229667

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pyx_pxy_pyx_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq9 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq42 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq42 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq56 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq56
    | (have j0 := eq56 (σ X0) (σ X1)
       grind)
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq43 (τ X0)
       grind)
    | exact superpose eq43 eq18
    | exact resolve eq18 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq83 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq83
    | exact resolve eq83 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq83
  have eq95 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq91
    | exact resolve eq91 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq109 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 (M.op X1 X2)) X0) = (M.op (M.op X4 (M.op X1 X2)) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq23 X2 X4 X1 x
       have i₂ := eq23 X2 X0 X1 x
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (M.op X0 X1) x X1 X2
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) (M.op X4 (M.op X3 X4)))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X3 (M.op X1 X2) X2 X4
       have i₂ := eq23 X1 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq23 eq24
    | exact resolve eq24 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X0 X2)) (M.op (M.op X4 (M.op X5 X4)) (M.op X3 (M.op X0 (M.op X1 (M.op X2 X1)))))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq24 (M.op X3 (M.op X0 X2)) X4 X5 X3
       have i₂ := eq23 X2 X3 X0 X1
       grind)
    | exact superpose eq23 eq24
    | exact resolve eq24 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq169 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67 y x
       grind)
    | exact superpose eq67 eq16
    | (have j1 := eq67 y x
       grind)
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq189 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq9
    | exact resolve eq9 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op X1 (M.op (σ (M.op X0 X0)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq189 X0 x
       have i₂ := eq23 (σ (M.op X0 X0)) x (σ X0) X1
       grind)
    | exact superpose eq23 eq189
    | exact resolve eq189 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq518 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq169
       have i₂ := eq95 x
       grind)
    | exact superpose eq95 eq169
    | exact resolve eq169 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq545 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq518
       have i₂ := eq56 y x
       grind)
    | exact superpose eq56 eq518
    | (have j1 := eq56 y x
       grind)
    | exact resolve eq518 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq518
  have eq546 : (M.op x x) = (M.op y x) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by grind
  clear eq545
  have eq561 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ (M.op X0 X0))) (M.op X1 (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq116 X1 (M.op (σ X0) (σ (M.op X0 X0))) X1
       have i₂ := eq189 X0 X1
       grind)
    | exact superpose eq189 eq116
    | exact resolve eq116 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq989 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X0) X3) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq109 X0 (M.op (σ X0) (σ (M.op X0 X0))) (M.op X1 (σ X0)) x
       have i₂ := eq561 X0 X1
       grind)
    | exact superpose eq561 eq109
    | exact resolve eq109 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq561
  have eq1473 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq116 X2 X1 X2
       have i₂ := eq989 X1 X0 X2
       grind)
    | (have i₁ := eq116 X2 X1 X2
       have i₂ := eq989 X1 X2 X0
       grind)
    | exact superpose eq989 eq116
    | exact resolve eq116 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq2375 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (M.op X0 X1) X0) X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1473 (M.op (M.op X0 X1) X0) X2 X1
       have i₂ := eq1473 X0 X1 (M.op (M.op (M.op X0 X1) X0) X2)
       grind)
    | exact superpose eq1473 eq1473
    | exact resolve eq1473 eq1473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq13589 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op (M.op X2 (M.op (M.op X3 X0) X3)) X2) X1)) (M.op (M.op X4 (M.op X5 X4)) X0)) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq136 (M.op (M.op X2 (M.op (M.op X3 X0) X3)) X2) x X1 X1 X4 X5
       have i₂ := eq134 X2 X3 X0 X1 x
       grind)
    | exact superpose eq134 eq136
    | exact resolve eq136 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq136
  have eq13925 : ∀ X0 X3 X4 X5 : G, (M.op (M.op (M.op X3 X0) X3) (M.op (M.op X4 (M.op X5 X4)) X0)) = X5 := by
    intro X0 X3 X4 X5
    first
    | (have i₁ := eq13589 X0 x x X3 X4 X5
       have i₂ := eq2375 x (M.op (M.op X3 X0) X3) x
       grind)
    | exact superpose eq2375 eq13589
    | exact resolve eq13589 eq2375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2375 eq13589
  have eq43187 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op x (M.op x x)) X1)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq13925 X1 X0 x y
       have i₂ := eq546
       grind)
    | exact superpose eq546 eq13925
    | exact resolve eq13925 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq43190 : x = y ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43187 x x
       have i₂ := eq13925 x x x x
       grind)
    | (have i₁ := eq43187 x x
       have i₂ := eq13925 x x x (M.op (M.op (M.op x x) x) (M.op (M.op x (M.op x x)) x))
       grind)
    | exact superpose eq13925 eq43187
    | exact resolve eq43187 eq13925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13925 eq43187
  have eq43226 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq43190
       grind)
    | exact superpose eq43190 eq16
    | exact resolve eq16 eq43190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43190
  have eq43227 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq43226
       have r₂ := eq95 x
       grind)
    | exact resolve eq43226 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43226
  have eq43397 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op X0 (M.op (σ (M.op x x)) X0))) := by
    intro X0
    first
    | (have i₁ := eq116 (σ y) (σ x) X0
       have i₂ := eq43227
       grind)
    | exact superpose eq43227 eq116
    | exact resolve eq116 eq43227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq43227
  have eq43494 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq43397 x
       have i₂ := eq387 x x
       grind)
    | exact superpose eq387 eq43397
    | exact resolve eq43397 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387 eq43397
  have eq43557 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq43494
       grind)
    | exact superpose eq43494 eq10
    | exact resolve eq10 eq43494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43494
  have eq43613 : x = y := by
    first
    | (have i₁ := eq43557
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq43557
    | exact resolve eq43557 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43557
  have eq45324 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq43613
       grind)
    | exact superpose eq43613 eq16
    | exact resolve eq16 eq43613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43613
  have eq45327 : False := by grind
  exact eq45327

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pxy_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  clear eq43
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
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
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X1)) X3
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
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) ∨ y = (M.op y y) := by
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
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq78
    | exact resolve eq78 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq84 : (M.op y y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq83
    | exact resolve eq83 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq96 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq105 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq105 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq105 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq105 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq108 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq106 (σ X0)
       grind)
    | exact superpose eq106 eq10
    | exact resolve eq10 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq106 sF2
       grind)
    | exact superpose eq106 eq49
    | exact resolve eq49 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq112 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq111
       have i₂ := eq106 x
       grind)
    | exact superpose eq106 eq111
    | exact resolve eq111 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq115 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq108 X0
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq108
    | exact resolve eq108 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq120 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq96
       have i₂ := eq106 sF3
       grind)
    | exact superpose eq106 eq96
    | exact resolve eq96 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq121 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq120
       have i₂ := eq106 y
       grind)
    | exact superpose eq106 eq120
    | exact resolve eq120 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq120
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
  have eq249 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 (M.op X1 X0)) (M.op y (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (σ x))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op (σ y) (M.op (σ x) (σ y)))))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) (M.op X3 (M.op X1 X3))) = (M.op (M.op X4 X0) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X1 X4 (M.op X1 (M.op X2 (M.op X0 X2))) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 X2))) = (M.op X0 (M.op (M.op X1 X3) (M.op X4 (M.op X0 X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X3 (M.op (M.op X1 X3) (M.op X4 (M.op X0 X4))) X1 X2
       have i₂ := eq14 X0 (M.op X1 X3) X4
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X1) x X1 X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 x
       have i₂ := eq52 X2 X0 X1 x
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0)) X3) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3 (M.op X1 X2)
       have i₂ := eq52 X1 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq472 : ∀ X0 X1 X2 : G, (σ x) = (M.op (M.op X0 (M.op X1 (M.op X2 X1))) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op (M.op sF3 sF4) (M.op X2 X0))
       have i₂ := eq52 X0 (M.op sF3 sF4) X2 x
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) (M.op X4 (M.op X3 X4)))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X3 (M.op X1 X2) X2 X4
       have i₂ := eq52 X1 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op y (M.op x y))) (M.op (M.op X1 (M.op X2 X1)) (M.op X0 x))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X4) = (M.op (M.op X1 (M.op X0 X1)) (M.op X2 (M.op (M.op X3 (M.op X4 X3)) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X3 (M.op X4 X3)) X4 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq53 X4 X1 X0 X3
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq602 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq1053 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq452 X2 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq452
    | exact resolve eq452 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1055 : ∀ X0 : G, (M.op (M.op y (M.op x y)) (M.op X0 x)) = X0 := by
    intro X0
    first
    | exact superpose eq50 eq452
    | exact resolve eq452 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1056 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op X0 (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq452
    | exact resolve eq452 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1077 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 x) X0)) := by
    intro X0
    first
    | exact superpose eq1055 eq452
    | exact resolve eq452 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055
  have eq1090 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq1056 eq452
    | exact resolve eq452 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056
  have eq1108 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | exact superpose eq1077 eq14
    | exact resolve eq14 eq1077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq1141 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X3) X0)) X1)) X2) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq457 (M.op (M.op X1 (M.op (M.op X2 X3) X0)) X1) X2 X3
       have i₂ := eq457 X1 (M.op X2 X3) X0
       grind)
    | exact superpose eq457 eq457
    | exact resolve eq457 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1220 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq1090 eq14
    | exact resolve eq14 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1236 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (M.op y y)) := by
    first
    | (have i₁ := eq1108 (M.op y y)
       have i₂ := eq1108 y
       grind)
    | exact superpose eq1108 eq1108
    | exact resolve eq1108 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1238 : ∀ X0 : G, (M.op y (M.op X0 (M.op (M.op x y) x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq452 X0 y X0
       have i₂ := eq1108 X0
       grind)
    | (have i₁ := eq452 x y x
       have i₂ := eq1108 X0
       grind)
    | exact superpose eq1108 eq452
    | exact resolve eq452 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108
  have eq1268 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x)))) = X0 := by
    intro X0
    first
    | exact superpose eq1220 eq452
    | exact resolve eq452 eq1220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220
  have eq1507 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X1) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq452 X2 (M.op X1 X2) (M.op X0 X1)
       have i₂ := eq1053 X1 X2 X0
       grind)
    | exact superpose eq1053 eq452
    | exact resolve eq452 eq1053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1514 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1238 (M.op x (M.op x x))
       have i₂ := eq1053 x x sF0
       grind)
    | exact superpose eq1053 eq1238
    | exact resolve eq1238 eq1053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238
  have eq1516 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq1268 (M.op x (M.op sF2 x))
       have i₂ := eq1053 sF2 x sF4
       grind)
    | exact superpose eq1053 eq1268
    | exact resolve eq1268 eq1053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053 eq1268
  have eq1612 : ∀ X0 X1 : G, (M.op y (M.op x y)) = (M.op (M.op X0 x) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq249 eq457
    | exact resolve eq457 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq1866 : ∀ X0 : G, (M.op (M.op (M.op y (M.op x y)) X0) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq457 X0 x X0
       have i₂ := eq1514 X0
       grind)
    | (have i₁ := eq457 y x y
       have i₂ := eq1514 X0
       grind)
    | exact superpose eq1514 eq457
    | exact resolve eq457 eq1514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1514
  have eq1917 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq1516 eq457
    | exact resolve eq457 eq1516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457 eq1516
  have eq2990 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X1) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq452 X2 X0 (M.op (M.op X1 X2) X1)
       have i₂ := eq1507 X1 X2 X0
       grind)
    | exact superpose eq1507 eq452
    | exact resolve eq452 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452 eq1507
  have eq9637 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq433 (M.op X1 (M.op x X1)) sF4 sF3
       have i₂ := eq53 sF3 X1 x sF4
       grind)
    | exact superpose eq53 eq433
    | exact resolve eq433 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq433
  have eq15195 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) X1) (M.op X0 (M.op y (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq508 eq458
    | exact resolve eq458 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq18098 : ∀ X0 X1 X2 X3 : G, (σ x) = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (M.op X2 (M.op X3 (M.op X1 X3))) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq472 (M.op X2 (M.op X3 (M.op X1 X3))) x X2
       have i₂ := eq441 X1 X2 X3 x X0
       grind)
    | exact superpose eq441 eq472
    | exact resolve eq472 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq18353 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op (σ y) (M.op (σ x) (σ y))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18098 X0 X1 x x
       have i₂ := eq14 X1 x x
       grind)
    | exact superpose eq14 eq18098
    | exact resolve eq18098 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18098
  have eq25031 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op (M.op X6 (M.op X4 (M.op X1 X4))) X6) = (M.op (M.op X0 X1) (M.op X5 (M.op (M.op X2 (M.op X0 X2)) X5))) := by
    intro X0 X1 X2 X4 X5 X6
    first
    | (have i₁ := eq441 (M.op X4 (M.op X1 X4)) (M.op X2 (M.op X0 X2)) x X5 X6
       have i₂ := eq520 X0 X2 x X4 X1
       grind)
    | exact superpose eq520 eq441
    | exact resolve eq441 eq520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441 eq520
  have eq25179 : ∀ X0 X1 X2 X5 : G, (M.op (M.op X0 X1) (M.op X5 (M.op (M.op X2 (M.op X0 X2)) X5))) = X1 := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq25031 X0 X1 X2 x X5 x
       have i₂ := eq14 X1 x x
       grind)
    | exact superpose eq14 eq25031
    | exact resolve eq25031 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25031
  have eq85545 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op X1 X0) X1)) (σ y)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9637 (M.op (M.op sF4 sF2) (M.op (M.op X1 x) X1)) (M.op sF4 sF2)
       have i₂ := eq458 (M.op sF4 sF2) X1 x (M.op sF4 sF2)
       grind)
    | exact superpose eq458 eq9637
    | exact resolve eq9637 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq94262 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op (M.op x y) x) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq15195 eq448
    | exact resolve eq448 eq15195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448 eq15195
  have eq99819 : ∀ X0 X1 : G, (M.op y (M.op x y)) = (M.op (M.op (M.op (M.op X0 X1) X0) x) (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) X1) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq18353 eq1612
    | exact resolve eq1612 eq18353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612 eq18353
  have eq99854 : ∀ X0 X1 : G, (M.op y (M.op x y)) = (M.op (M.op (M.op (M.op X0 X1) X0) x) X1) := by
    intro X0 X1
    first
    | exact superpose eq1917 eq99819
    | exact resolve eq99819 eq1917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1917 eq99819
  have eq152975 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op X0 X1) (σ y))) X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq9637 eq1141
    | exact resolve eq1141 eq9637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141 eq9637
  have eq420206 : ∀ X0 X1 : G, y = (M.op (M.op y x) (M.op X0 (M.op (M.op X1 (M.op y X1)) X0))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq25179 y y X1 X0
       have i₂ := eq84
       grind)
    | exact superpose eq84 eq25179
    | exact resolve eq25179 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq420263 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq420206 x x
       have i₂ := eq25179 y x x x
       grind)
    | exact superpose eq25179 eq420206
    | exact resolve eq420206 eq25179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25179 eq420206
  have eq449594 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq420263 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq420263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420263
  have eq449601 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq449594
    | exact resolve eq449594 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449594
  have eq449612 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq449601
       have r₂ := eq27
       grind)
    | exact resolve eq449601 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449601
  have eq449871 : (σ y) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ y) (σ x)) (σ y))) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq449612 eq152975
    | exact resolve eq152975 eq449612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152975 eq449612
  have eq449877 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq85545 eq449871
    | exact resolve eq449871 eq85545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85545 eq449871
  have eq450044 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq449877 eq121
    | exact resolve eq121 eq449877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq449877
  have eq450413 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq450044
    | exact resolve eq450044 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450044
  have eq450414 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq450413
  have eq450509 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq450414
       grind)
    | exact superpose eq450414 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq450414
       grind)
    | exact resolve eq13 eq450414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq450511 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq602 y X0
       have i₂ := eq450414
       grind)
    | exact superpose eq450414 eq602
    | (have j0 := eq602 y X0
       grind)
    | exact resolve eq602 eq450414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq450710 : y = (M.op (M.op (M.op x y) x) (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq94262 y y
       have i₂ := eq450414
       grind)
    | exact superpose eq450414 eq94262
    | exact resolve eq94262 eq450414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94262 eq450414
  have eq450731 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq450511 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450511
  have eq450732 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq450509 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450509
  have eq450741 : y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1236 eq450710
    | exact resolve eq450710 eq1236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236 eq450710
  have eq450826 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq450731 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq450731
    | (have j0 := eq450731 X0
       grind)
    | exact resolve eq450731 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450731
  have eq451058 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) (M.op x y))) = X2 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2
    first
    | exact superpose eq450741 eq503
    | exact resolve eq503 eq450741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq451203 : (M.op y (M.op x y)) = (M.op (M.op (M.op y (M.op x y)) x) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq450741 eq99854
    | exact resolve eq99854 eq450741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99854 eq450741
  have eq451229 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1866 eq451203
    | exact resolve eq451203 eq1866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1866 eq451203
  have eq451341 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) (M.op x y))) = X2 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq451058 X0 X1 X2
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq451058
    | (have j0 := eq451058 X0 X1 X2
       grind)
    | exact resolve eq451058 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451058
  have eq451484 : ∀ X1 X2 : G, (M.op (M.op X1 X2) X1) = X2 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1 X2
    first
    | (have i₁ := eq451341 X1 X1 X2
       have i₂ := eq2990 sF0 X1 (M.op (M.op X1 X2) X1)
       grind)
    | exact superpose eq2990 eq451341
    | exact resolve eq451341 eq2990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2990 eq451341
  have eq473674 : (σ (M.op y (M.op x y))) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq130
       have i₂ := eq450732 sF0
       grind)
    | exact superpose eq450732 eq130
    | exact resolve eq130 eq450732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq450732
  have eq857552 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq451229 eq473674
    | exact resolve eq473674 eq451229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451229 eq473674
  have eq857633 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq857552
  have eq857640 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq857633
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq857633
    | exact resolve eq857633 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857633
  have eq857652 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq857640 eq450826
    | exact resolve eq450826 eq857640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450826 eq857640
  have eq857660 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq857652
  have eq857988 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq857660 eq451484
    | exact resolve eq451484 eq857660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451484 eq857660
  have eq857991 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq857988
  have eq857993 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq857991
    | exact resolve eq857991 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857991
  have eq858153 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq857993
       have r₂ := eq27
       grind)
    | exact resolve eq857993 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857993
  have eq858219 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq858153 eq29
    | exact resolve eq29 eq858153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq858153
  have eq858612 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq858219
    | exact resolve eq858219 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq858219
  have eq858613 : x = y := by grind
  clear eq858612
  have eq858644 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq858613
       grind)
    | exact superpose eq858613 eq18
    | exact resolve eq18 eq858613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq858645 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq858613
       grind)
    | exact superpose eq858613 eq24
    | exact resolve eq24 eq858613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq858613
  have eq859050 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq858645
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq858645
    | exact resolve eq858645 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq858645
  have eq859115 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq859050 eq26
    | exact resolve eq26 eq859050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq859050
  have eq860555 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq859115 eq112
    | exact resolve eq112 eq859115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq859115
  have eq861259 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq860555
       have i₂ := eq858644
       grind)
    | exact superpose eq858644 eq860555
    | exact resolve eq860555 eq858644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858644 eq860555
  have eq861505 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq861259 eq15
    | exact resolve eq15 eq861259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861259
  have eq861589 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq861505
    | exact resolve eq861505 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq861505
  have eq861610 : False := by grind
  exact eq861610

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
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
  have eq165 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
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
  have eq241 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq165
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq165
    | (have j1 := eq79 (σ x) (σ y)
       grind)
    | (have r₁ := eq165
       have r₂ := eq79 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq165
       have r₂ := eq79 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq165 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq165
  have eq244 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq241
  have eq245 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq244
       grind)
    | exact superpose eq244 eq16
    | exact resolve eq16 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq246 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq245
       have r₂ := eq65 x
       grind)
    | exact resolve eq245 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq282 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq246
       grind)
    | exact superpose eq246 eq10
    | exact resolve eq10 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq299 : x = y := by
    first
    | (have i₁ := eq282
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq282
    | exact resolve eq282 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq343 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq299
       grind)
    | exact superpose eq299 eq16
    | exact resolve eq16 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq344 : False := by grind
  exact eq344

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pyx_pxy_Equation2373 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq9 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq29
    | (have j0 := eq29 X0 X1
       grind)
    | exact resolve eq29 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq72 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = (M.op (M.op X2 (M.op X1 (σ X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (σ X0) X2 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) (M.op X4 (M.op X3 X4)))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 X3 (M.op X1 X2) X2 X4
       have i₂ := eq24 X1 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq24 eq25
    | exact resolve eq25 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq216 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq38
    | (have j0 := eq38 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | exact resolve eq38 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1988 : ∀ X0 X1 X2 X3 : G, (σ X1) = (M.op X2 (M.op (M.op (M.op X0 (M.op (σ (M.op X1 X1)) (σ X1))) X0) (M.op X3 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X2 (σ (M.op X1 X1)) (σ X1) X3
       have i₂ := eq72 X1 (σ (M.op X1 X1)) X0
       grind)
    | exact superpose eq72 eq25
    | exact resolve eq25 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq72
  have eq70480 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq216 x y
       grind)
    | exact superpose eq216 eq16
    | (have j1 := eq216 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq216 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq216 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq216 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq70686 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq70480
  have eq216296 : ∀ X0 X1 X2 : G, (σ y) = (M.op X0 (M.op (M.op (M.op X1 (M.op (σ (M.op x x)) (σ x))) X1) (M.op X2 (M.op X0 X2)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq112 X1 (σ x) (σ y) X0 X2
       have i₂ := eq70686
       grind)
    | exact superpose eq70686 eq112
    | exact resolve eq112 eq70686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70686
  have eq216603 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq216296 x x x
       have i₂ := eq1988 x x x x
       grind)
    | exact superpose eq1988 eq216296
    | exact resolve eq216296 eq1988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1988 eq216296
  have eq216604 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq216603
  have eq251553 : ∀ X0 X1 X2 : G, y = (M.op X0 (M.op (M.op (M.op X1 (M.op (M.op x x) x)) X1) (M.op X2 (M.op X0 X2)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq112 X1 x y X0 X2
       have i₂ := eq216604
       grind)
    | exact superpose eq216604 eq112
    | exact resolve eq112 eq216604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216604
  have eq251870 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq251553 x x x
       have i₂ := eq112 x x x x x
       grind)
    | exact superpose eq112 eq251553
    | exact resolve eq251553 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq251553
  have eq251871 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq251870
  have eq281179 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq251871
       grind)
    | exact superpose eq251871 eq10
    | exact resolve eq10 eq251871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251871
  have eq281297 : x = y ∨ x = y := by
    first
    | (have i₁ := eq281179
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq281179
    | exact resolve eq281179 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281179
  have eq281298 : x = y := by grind
  clear eq281297
  have eq294298 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq281298
       grind)
    | exact superpose eq281298 eq16
    | exact resolve eq16 eq281298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281298
  have eq294299 : False := by grind
  exact eq294299

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_y_pyx_Equation2373 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = b :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq99
    | exact resolve eq99 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq100
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq555 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 (M.op X0 X1) x X1 X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq911 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq555 X2 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq555
    | exact resolve eq555 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq1350 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y X0)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq911 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq911
    | (have j0 := eq911 y X0 x
       grind)
    | exact resolve eq911 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1356 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq911
    | (have j0 := eq911 (σ y) X0 (σ x)
       grind)
    | exact resolve eq911 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64000 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq64007 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq64000
    | exact resolve eq64000 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64000
  have eq64018 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq64007
       have r₂ := eq28
       grind)
    | exact resolve eq64007 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64007
  have eq64022 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq64018
    | exact resolve eq64018 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64018
  have eq64125 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ y) X0)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq64022 eq911
    | exact resolve eq911 eq64022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64022
  have eq64139 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq1356 eq64125
    | exact resolve eq64125 eq1356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1356 eq64125
  have eq64140 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq64139
  have eq64264 : ∀ X0 : G, y = (M.op (M.op X0 (M.op y X0)) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq911 y X0 y
       have i₂ := eq64140
       grind)
    | exact superpose eq64140 eq911
    | exact resolve eq911 eq64140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911 eq64140
  have eq64277 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1350 eq64264
    | exact resolve eq64264 eq1350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350 eq64264
  have eq64278 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq64277
  have eq64322 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq64278 eq30
    | exact resolve eq30 eq64278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq64278
  have eq64488 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq64322
    | exact resolve eq64322 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq64322
  have eq64489 : x = y := by grind
  clear eq64488
  have eq64641 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq64489
       grind)
    | exact superpose eq64489 eq19
    | exact resolve eq19 eq64489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq64642 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq64489
       grind)
    | exact superpose eq64489 eq25
    | exact resolve eq25 eq64489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq64489
  have eq64805 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq64642
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq64642
    | exact resolve eq64642 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq64642
  have eq64824 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq64805 eq27
    | exact resolve eq27 eq64805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq64805
  have eq65309 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq64824 eq68
    | exact resolve eq68 eq64824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq64824
  have eq65490 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq65309
       have i₂ := eq64641
       grind)
    | exact superpose eq64641 eq65309
    | exact resolve eq65309 eq64641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64641 eq65309
  have eq65547 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq65490 eq15
    | exact resolve eq15 eq65490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65490
  have eq65593 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq65547
    | exact resolve eq65547 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq65547
  have eq65602 : False := by grind
  exact eq65602

/-- `Equation2452`: `x = (x ◇ ((x ◇ y) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pyx_pyy_pyx_Equation2452 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq63 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op (M.op X0 x) x) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, X0 ≠ X0 ∨ (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq63 X0
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq68 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq67 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq292 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq14 (M.op X0 (M.op X1 X1)) X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq301 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq306 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq292 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq307 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq306 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq308 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq302 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq302 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq302 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq323 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq308 (σ X0)
       grind)
    | exact superpose eq308 eq15
    | exact resolve eq15 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq323 X0
       have i₂ := eq308 X0
       grind)
    | exact superpose eq308 eq323
    | exact resolve eq323 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308 eq323
  have eq391 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq68 (σ X0)
       have i₂ := eq342 X0
       grind)
    | exact superpose eq342 eq68
    | exact resolve eq68 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq394 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq391 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq391
    | exact resolve eq391 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq398 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq394 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq394
    | exact resolve eq394 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq394
  have eq477 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq307 (σ X0) (σ X1)
       grind)
    | exact superpose eq307 eq15
    | (have j1 := eq307 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq307 X0 (τ X1)
       grind)
    | exact superpose eq307 eq18
    | (have j1 := eq307 X0 (τ X1)
       grind)
    | exact resolve eq18 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq307
  have eq494 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq477 X0 X1
       have i₂ := eq342 X0
       grind)
    | exact superpose eq342 eq477
    | (have j0 := eq477 X0 X1
       grind)
    | exact resolve eq477 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq477
  have eq680 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq485 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq485
    | exact resolve eq485 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq740 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq680 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq680
    | (have j0 := eq680 X0 X1
       grind)
    | exact resolve eq680 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq1237 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq494 x y
       grind)
    | exact superpose eq494 eq16
    | (have j1 := eq494 x y
       grind)
    | exact resolve eq16 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq1312 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1237
       have i₂ := eq740 y x
       grind)
    | exact superpose eq740 eq1237
    | (have j1 := eq740 y x
       grind)
    | (have r₁ := eq1237
       have r₂ := eq740 y x
       grind)
    | exact resolve eq1237 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740 eq1237
  have eq1313 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq1312
  have eq1322 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq398 x
       have i₂ := eq1313
       grind)
    | exact superpose eq1313 eq398
    | exact resolve eq398 eq1313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313
  have eq1338 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq1322
       have r₂ := eq16
       grind)
    | exact resolve eq1322 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322
  have eq1345 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1338
       grind)
    | exact superpose eq1338 eq10
    | exact resolve eq10 eq1338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338
  have eq1390 : y = (M.op x x) := by
    first
    | (have i₁ := eq1345
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1345
    | exact resolve eq1345 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345
  have eq1398 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq398 x
       have i₂ := eq1390
       grind)
    | exact superpose eq1390 eq398
    | exact resolve eq398 eq1390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398 eq1390
  have eq1414 : False := by grind
  exact eq1414

/-- `Equation2452`: `x = (x ◇ ((x ◇ y) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pyx_pxy_pyx_Equation2452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
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
  have eq69 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq237 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq69 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq69 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq69 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq69 X0 X1
       grind)
    | exact resolve eq13 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq255 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq237 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq256 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq255 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq261 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq256 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq256 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq256 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq269 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq261 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq261
    | (have j0 := eq261 X0 X1
       grind)
    | exact resolve eq261 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq270 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq269 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq275 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq270 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq270
    | exact resolve eq270 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq270 x y
       grind)
    | exact superpose eq270 eq16
    | exact resolve eq16 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq363 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq275 X0 (τ X1)
       grind)
    | exact superpose eq275 eq17
    | exact resolve eq17 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq275
  have eq379 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq363 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq363
    | exact resolve eq363 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq386 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq379 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq379
    | exact resolve eq379 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq440 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq287
       have i₂ := eq386 x y
       grind)
    | exact superpose eq386 eq287
    | exact resolve eq287 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287 eq386
  have eq441 : False := by grind
  exact eq441
