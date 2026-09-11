import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_x_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq66 (σ X0)
       grind)
    | exact superpose eq66 eq10
    | exact resolve eq10 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq49
    | exact resolve eq49 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq70
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq70
    | exact resolve eq70 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq68
    | exact resolve eq68 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ (M.op y x) = (M.op y y) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq89
    | exact resolve eq89 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq95 : (M.op y x) = (M.op y y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq94
    | exact resolve eq94 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq236 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq50 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq51 (M.op sF4 sF4)
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op X1 X0) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq249 eq14
    | exact resolve eq14 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq312 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq66 (τ X0)
       grind)
    | exact superpose eq66 eq34
    | exact resolve eq34 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq323 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq312 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq312
    | exact resolve eq312 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq326 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq323 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq323
    | exact resolve eq323 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq323
  have eq517 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq526 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq529 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq53 (σ X0) (σ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq53
    | exact resolve eq53 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq583 X0
       have i₂ := eq73 (M.op X0 X0)
       grind)
    | exact superpose eq73 eq583
    | exact resolve eq583 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq583
  have eq602 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq593 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq593
    | exact resolve eq593 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq735 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq52 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq753 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3 X4
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq760 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq761 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X4 X2 X3 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq53 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq52 X0 x x X3
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq776 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq777 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq782 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq777 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq777
    | exact resolve eq777 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq783 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq776 X0 X1 X2 X3
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq776
    | exact resolve eq776 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq791 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq761 X0 X1 X2 X3 X4
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq761
    | exact resolve eq761 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq792 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq753 X0 X1 X2 X3 X4
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq753
    | exact resolve eq753 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq812 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq326 X0
       grind)
    | exact superpose eq326 eq16
    | exact resolve eq16 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq970 : ∀ X0 : G, (τ X0) = (M.op y (M.op (M.op x y) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq50 (τ X0)
       have i₂ := eq812 X0
       grind)
    | exact superpose eq812 eq50
    | exact resolve eq50 eq812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq1621 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq529 (M.op x sF4) (M.op x sF4)
       have i₂ := eq14 (M.op x sF4) sF4 x
       grind)
    | exact superpose eq14 eq529
    | exact resolve eq529 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq1631 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1621 X0
       have i₂ := eq53 X0 sF4
       grind)
    | exact superpose eq53 eq1621
    | exact resolve eq1621 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1621
  have eq1797 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq735 X1 (M.op X0 (M.op X0 X0)) X2
       have i₂ := eq735 X0 X0 X0
       grind)
    | exact superpose eq735 eq735
    | exact resolve eq735 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1818 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq735 X1 X2 (M.op X0 (M.op X0 X0))
       have i₂ := eq735 X0 X0 X0
       grind)
    | exact superpose eq735 eq735
    | exact resolve eq735 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1849 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq735 X0 X0 X0
       grind)
    | exact superpose eq735 eq14
    | exact resolve eq14 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1850 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq735 X0 X0 X0
       grind)
    | exact superpose eq735 eq50
    | exact resolve eq50 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1851 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq735 X0 X0 X0
       grind)
    | exact superpose eq735 eq51
    | exact resolve eq51 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1859 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq517 (M.op x (M.op x x))
       have i₂ := eq735 x x x
       grind)
    | exact superpose eq735 eq517
    | exact resolve eq517 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq1864 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq771 (M.op x (M.op x x)) x
       have i₂ := eq735 x x x
       grind)
    | exact superpose eq735 eq771
    | exact resolve eq771 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq2102 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq526 X0
       have i₂ := eq1850 X0
       grind)
    | exact superpose eq1850 eq526
    | exact resolve eq526 eq1850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2308 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1851 X0
       have i₂ := eq1850 X0
       grind)
    | exact superpose eq1850 eq1851
    | exact resolve eq1851 eq1850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1851
  have eq2422 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1859 (M.op (M.op x sF0) (M.op X0 X0))
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq1859
    | exact resolve eq1859 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1859
  have eq2468 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op X1 (M.op x y)) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2422 X0 X1
       have i₂ := eq1850 (M.op (M.op X1 sF0) (M.op X0 X0))
       grind)
    | exact superpose eq1850 eq2422
    | exact resolve eq2422 eq1850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2422
  have eq2482 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X0 X0)) = (M.op X0 (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2468 X0 x
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq2468
    | exact resolve eq2468 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2468
  have eq2594 : y = (M.op (M.op x y) (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq1864 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1864
    | (have j0 := eq1864 y x
       grind)
    | exact resolve eq1864 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2608 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq26 eq1864
    | (have j0 := eq1864 (σ y) (σ x)
       grind)
    | exact resolve eq1864 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2635 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1864 X0 X1
       have i₂ := eq1850 X0
       grind)
    | exact superpose eq1850 eq1864
    | exact resolve eq1864 eq1850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2670 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) := by
    first
    | (have i₁ := eq2608
       have i₂ := eq1850 sF3
       grind)
    | exact superpose eq1850 eq2608
    | exact resolve eq2608 eq1850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2608
  have eq2929 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | exact superpose eq970 eq2102
    | exact resolve eq2102 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970 eq2102
  have eq4468 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq532 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq532 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq532 eq532
    | exact resolve eq532 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq5908 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq51 eq760
    | exact resolve eq760 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq5967 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op X0 X1) (M.op (σ y) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq249 eq5908
    | exact resolve eq5908 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5908
  have eq6105 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq783 X0 X1 X2 X3
       have i₂ := eq782 X0 X1
       grind)
    | exact superpose eq782 eq783
    | exact resolve eq783 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq6275 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X1 (M.op X0 X0)))) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6105 X1 (M.op X0 X0) (M.op X1 X1) x
       have i₂ := eq735 x X1 X0
       grind)
    | exact superpose eq735 eq6105
    | exact resolve eq6105 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6299 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op X2 X1)) (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6105 (M.op X3 (M.op X2 X1)) (M.op X0 X0) X1 X2
       have i₂ := eq14 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq14 eq6105
    | exact resolve eq6105 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6354 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X2 (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X1 X2)) X2 X1
       have i₂ := eq6105 X0 (M.op X1 X2) (M.op X1 X2) X0
       grind)
    | exact superpose eq6105 eq14
    | exact resolve eq14 eq6105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6105
  have eq8363 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq791 X0 X1 X2 X3 X4
       have i₂ := eq782 X0 X1
       grind)
    | exact superpose eq782 eq791
    | exact resolve eq791 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq8569 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) X0)) = (M.op (M.op (M.op X1 X2) (M.op X3 X3)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8363 X0 (M.op X0 (M.op X0 X0)) X2 X3 x
       have i₂ := eq526 X0
       grind)
    | exact superpose eq526 eq8363
    | exact resolve eq8363 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8363
  have eq9055 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) (M.op (M.op y (M.op (M.op x y) (M.op X0 X1))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq792 X0 X1 X2 X3 X4
       have i₂ := eq782 X0 X1
       grind)
    | exact superpose eq782 eq792
    | exact resolve eq792 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782 eq792
  have eq9179 : ∀ X0 X2 X3 : G, (M.op X0 (M.op (M.op y (M.op (M.op x y) (M.op X2 (M.op X0 X0)))) (M.op X3 X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq9055 X2 (M.op X0 X0) x (M.op X2 X2) X3
       have i₂ := eq735 x X2 X0
       grind)
    | exact superpose eq735 eq9055
    | exact resolve eq9055 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735 eq9055
  have eq29181 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq760 X0 (M.op X1 X0) X2 X3 X4
       have i₂ := eq1849 X0 X0 X1
       grind)
    | exact superpose eq1849 eq760
    | exact resolve eq760 eq1849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29265 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq29181 X0 X1 x x x
       have i₂ := eq760 X0 X0 x x x
       grind)
    | exact superpose eq760 eq29181
    | exact resolve eq29181 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760 eq29181
  have eq30424 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq5967 eq1849
    | exact resolve eq1849 eq5967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5967
  have eq30466 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1631 eq30424
    | exact resolve eq30424 eq1631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1631 eq30424
  have eq30469 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2308 eq30466
    | exact resolve eq30466 eq2308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30466
  have eq44938 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op y (M.op y y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1797 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1797
    | (have j0 := eq1797 y x X0
       grind)
    | exact resolve eq1797 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1797
  have eq46161 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2482 eq14
    | exact resolve eq14 eq2482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2482
  have eq46694 : ∀ X0 X1 : G, (M.op (M.op X1 y) X0) = (M.op (M.op x y) (M.op (M.op (M.op X1 y) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq46161 (M.op (M.op X1 y) X0)
       have i₂ := eq1849 X0 y X1
       grind)
    | exact superpose eq1849 eq46161
    | exact resolve eq46161 eq1849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1849
  have eq46829 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq46694 X0 X1
       have i₂ := eq1864 X0 (M.op X1 y)
       grind)
    | exact superpose eq1864 eq46694
    | exact resolve eq46694 eq1864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864 eq46694
  have eq47084 : ∀ X0 : G, (M.op y (M.op y y)) = (M.op (M.op X0 (M.op x x)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1818 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1818
    | (have j0 := eq1818 y X0 x
       grind)
    | exact resolve eq1818 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47114 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq1818
    | (have j0 := eq1818 (σ y) X0 (σ x)
       grind)
    | exact resolve eq1818 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47164 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 (M.op X1 X1)) (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq526 X2
       have i₂ := eq1818 X2 X0 X1
       grind)
    | exact superpose eq1818 eq526
    | exact resolve eq526 eq1818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq47700 : ∀ X0 : G, (M.op y (M.op (M.op x y) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq47114 X0
       have i₂ := eq1850 sF3
       grind)
    | exact superpose eq1850 eq47114
    | exact resolve eq47114 eq1850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47114
  have eq48761 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op x y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq46829 (M.op X0 y) X0
       have i₂ := eq53 X0 y
       grind)
    | exact superpose eq53 eq46829
    | exact resolve eq46829 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46829
  have eq68705 : y = (M.op (M.op x y) (M.op (M.op y (M.op y x)) (M.op y x))) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44938 y
       have i₂ := eq95
       grind)
    | exact superpose eq95 eq44938
    | exact resolve eq44938 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq44938
  have eq68849 : y = (M.op (M.op x y) (M.op (M.op y x) (M.op y x))) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq68705
       have i₂ := eq29265 (M.op y x) y
       grind)
    | exact superpose eq29265 eq68705
    | exact resolve eq68705 eq29265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68705
  have eq68883 : y = (M.op (M.op x y) (M.op x (M.op y x))) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq68849
       have i₂ := eq53 y x
       grind)
    | exact superpose eq53 eq68849
    | exact resolve eq68849 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68849
  have eq68901 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq46161 eq68883
    | exact resolve eq68883 eq46161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68883
  have eq70695 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq47164
    | (have j0 := eq47164 X0 (σ x) (σ y)
       grind)
    | exact resolve eq47164 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47164
  have eq79456 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 X0)) = (M.op y (M.op (M.op x y) (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq6275 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq4468 (M.op X1 X0) X1 X0
       grind)
    | exact superpose eq4468 eq6275
    | exact resolve eq6275 eq4468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4468
  have eq79548 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 X0)) = (M.op (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq6275 eq79456
    | exact resolve eq79456 eq6275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79456
  have eq79893 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq79548 X0 X1
       have i₂ := eq29265 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq29265 eq79548
    | exact resolve eq79548 eq29265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79548
  have eq79926 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq79893 X0 X1
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq79893
    | exact resolve eq79893 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79893
  have eq94381 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op X0 (M.op X0 X0))) (M.op X2 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6299 X2 (M.op X1 X0) (M.op x (M.op X1 X1)) X3
       have i₂ := eq1818 X0 x X1
       grind)
    | exact superpose eq1818 eq6299
    | exact resolve eq6299 eq1818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1818
  have eq94539 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op y (M.op (M.op x y) (M.op (M.op X2 (M.op X0 (M.op X0 X0))) (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1850 eq6299
    | exact resolve eq6299 eq1850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850
  have eq94542 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) (M.op (M.op X3 (M.op (M.op X0 X0) X1)) (M.op X2 X2)))) = (M.op (M.op (M.op x y) (M.op X0 (M.op X1 X1))) X2) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq6275 eq6299
    | exact resolve eq6299 eq6275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94592 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) (M.op (M.op X2 (M.op y (M.op (M.op x y) X0))) (M.op X1 X1)))) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq2308 eq6299
    | exact resolve eq6299 eq2308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94808 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op y (M.op (M.op x y) (M.op (σ y) (M.op X0 X0)))) := by
    intro X0
    first
    | exact superpose eq70695 eq6299
    | exact resolve eq6299 eq70695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70695
  have eq95143 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ y) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq6275 eq94808
    | exact resolve eq94808 eq6275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94808
  have eq95205 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq6299 eq94592
    | exact resolve eq94592 eq6299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94592
  have eq95225 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op x y) (M.op X0 (M.op X1 X1))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq6299 eq94542
    | exact resolve eq94542 eq6299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94542
  have eq95227 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq6299 eq94539
    | exact resolve eq94539 eq6299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94539
  have eq95262 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq6299 eq94381
    | exact resolve eq94381 eq6299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94381
  have eq96127 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq95143 (M.op x sF3)
       have i₂ := eq79926 sF3 x
       grind)
    | exact superpose eq79926 eq95143
    | exact resolve eq95143 eq79926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79926 eq95143
  have eq103310 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq95262 X1 X0 X2
       have i₂ := eq95262 X1 X3 X2
       grind)
    | (have i₁ := eq95262 X0 X1 X2
       have i₂ := eq95262 X0 X0 X2
       grind)
    | exact superpose eq95262 eq95262
    | exact resolve eq95262 eq95262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106597 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq6275 eq6354
    | exact resolve eq6354 eq6275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6275
  have eq106623 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X3)))) = (M.op (M.op (M.op x y) (M.op X0 (M.op X1 X2))) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq6354 eq6299
    | exact resolve eq6299 eq6354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6354
  have eq106820 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op x y) (M.op X0 (M.op X1 X2))) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq6299 eq106623
    | exact resolve eq106623 eq6299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106623
  have eq116937 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op y (M.op (M.op x y) (M.op (M.op y (M.op (M.op x y) (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq9179 eq2308
    | exact resolve eq2308 eq9179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2308 eq9179
  have eq116947 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X0) := by
    intro X0 X1
    first
    | exact superpose eq6299 eq116937
    | exact resolve eq116937 eq6299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6299 eq116937
  have eq117204 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op X1 (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0 X1
    first
    | exact superpose eq249 eq116947
    | exact resolve eq116947 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116947
  have eq131866 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X0) = (M.op (M.op (M.op x y) (M.op X1 (M.op (σ x) (σ y)))) X0) := by
    intro X0 X1
    first
    | exact superpose eq252 eq95225
    | exact resolve eq95225 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95225
  have eq132817 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X0) = (M.op (M.op (M.op x y) (M.op X1 (M.op (σ x) (σ y)))) X0) := by
    intro X0 X1
    first
    | exact superpose eq95205 eq131866
    | exact resolve eq131866 eq95205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95205 eq131866
  have eq132948 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op (σ y) (M.op (σ x) (σ y)))) X0) = (M.op (M.op (M.op x y) (M.op X1 (M.op (σ x) (σ y)))) X0) := by
    intro X0 X1
    first
    | exact superpose eq249 eq132817
    | exact resolve eq132817 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132817
  have eq133002 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op (M.op x y) (M.op X1 (M.op (σ x) (σ y)))) X0) := by
    intro X0 X1
    first
    | exact superpose eq117204 eq132948
    | exact resolve eq132948 eq117204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117204 eq132948
  have eq133093 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) X2) = (M.op (σ y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq133002 X2 X1
       have i₂ := eq103310 sF0 (M.op X1 sF4) X2 x
       grind)
    | (have i₁ := eq133002 X2 X1
       have i₂ := eq103310 X0 (M.op X1 sF4) X2 sF0
       grind)
    | exact superpose eq103310 eq133002
    | exact resolve eq133002 eq103310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133002
  have eq144882 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y (M.op (M.op x y) X0))) = (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq106597 (M.op X1 X1) (M.op X1 X0)
       have i₂ := eq8569 X0 X1 X1 X1
       grind)
    | exact superpose eq8569 eq106597
    | exact resolve eq106597 eq8569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8569
  have eq144901 : (M.op (M.op x y) (M.op y (M.op y y))) = (M.op (M.op x x) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq47084 eq106597
    | exact resolve eq106597 eq47084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47084
  have eq144910 : (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq47700 eq106597
    | exact resolve eq106597 eq47700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47700 eq106597
  have eq145600 : (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (M.op x y) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq144910
       have i₂ := eq95227 sF2 (M.op sF4 sF4)
       grind)
    | exact superpose eq95227 eq144910
    | exact resolve eq144910 eq95227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95227 eq144910
  have eq145608 : (M.op (M.op x y) (M.op y (M.op y y))) = (M.op (M.op x x) (M.op y (M.op x y))) := by
    first
    | exact superpose eq236 eq144901
    | exact resolve eq144901 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq144901
  have eq145621 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y (M.op (M.op x y) X0))) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq144882 X0 X1
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq144882
    | exact resolve eq144882 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq144882
  have eq145913 : (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (σ y)))) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq249 eq145600
    | exact resolve eq145600 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq145600
  have eq145918 : y = (M.op (M.op x x) (M.op y (M.op x y))) := by
    first
    | exact superpose eq2594 eq145608
    | exact resolve eq145608 eq2594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2594 eq145608
  have eq145931 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq2635 eq145621
    | exact resolve eq145621 eq2635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2635 eq145621
  have eq146072 : (σ y) = (M.op (M.op (M.op x y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2670 eq145913
    | exact resolve eq145913 eq2670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2670 eq145913
  have eq146518 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq145918
       have i₂ := eq95262 x x (M.op y sF0)
       grind)
    | (have i₁ := eq145918
       have i₂ := eq95262 x x (M.op y sF0)
       grind)
    | exact superpose eq95262 eq145918
    | exact resolve eq145918 eq95262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145918
  have eq146719 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq146072
       have i₂ := eq103310 sF0 sF2 (M.op sF3 sF4) x
       grind)
    | (have i₁ := eq146072
       have i₂ := eq103310 X0 sF2 (M.op sF3 sF4) sF0
       grind)
    | exact superpose eq103310 eq146072
    | exact resolve eq146072 eq103310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103310 eq146072
  have eq149845 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq252 eq145931
    | exact resolve eq145931 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq145931
  have eq151023 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq133093 eq149845
    | exact resolve eq149845 eq133093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133093 eq149845
  have eq223497 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq68901 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq68901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68901
  have eq223498 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq26 eq223497
    | exact resolve eq223497 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223497
  have eq223509 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq223498
       have r₂ := eq27
       grind)
    | exact resolve eq223498 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223498
  have eq223530 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq223509 eq30469
    | exact resolve eq30469 eq223509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30469
  have eq223700 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq223509 eq258
    | exact resolve eq258 eq223509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq223773 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op (M.op x y) (M.op X1 (M.op (σ y) (σ x)))) X0) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq223509 eq106820
    | exact resolve eq106820 eq223509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223788 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq106820 eq223773
    | exact resolve eq223773 eq106820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106820 eq223773
  have eq223824 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ x)) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq223700
       have i₂ := eq95262 sF2 sF3 (M.op sF3 sF4)
       grind)
    | exact superpose eq95262 eq223700
    | exact resolve eq223700 eq95262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223700
  have eq223926 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq223530
       have i₂ := eq95262 sF2 sF3 (M.op sF3 sF4)
       grind)
    | exact superpose eq95262 eq223530
    | exact resolve eq223530 eq95262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95262 eq223530
  have eq223951 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq146719 eq223824
    | exact resolve eq223824 eq146719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223824
  have eq224009 : (σ y) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq146719 eq223926
    | exact resolve eq223926 eq146719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223926
  have eq224058 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq223951 eq223509
    | exact resolve eq223509 eq223951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223509 eq223951
  have eq224299 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq224058
  have eq224621 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by grind
  have eq226703 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq224299 eq223788
    | exact resolve eq223788 eq224299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223788 eq224299
  have eq227387 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq226703
  have eq227682 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq227387
       have r₂ := eq224621
       grind)
    | exact resolve eq227387 eq224621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224621 eq227387
  have eq227941 : (σ x) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ y = (M.op y x) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq227682 eq50
    | exact resolve eq50 eq227682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq227682
  have eq246591 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = y ∨ y = (M.op y x) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq227941 eq224009
    | exact resolve eq224009 eq227941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224009 eq227941
  have eq246714 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by grind
  clear eq246591
  have eq246806 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq246714 eq151023
    | exact resolve eq151023 eq246714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151023 eq246714
  have eq246950 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq96127 eq246806
    | exact resolve eq246806 eq96127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96127 eq246806
  have eq246969 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq26 eq246950
    | exact resolve eq246950 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246950
  have eq247546 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq246969 eq146719
    | exact resolve eq146719 eq246969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146719 eq246969
  have eq247707 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq247546 x
       have i₂ := eq29265 sF2 x
       grind)
    | exact superpose eq29265 eq247546
    | exact resolve eq247546 eq29265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247546
  have eq250199 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq247707 eq2929
    | exact resolve eq2929 eq247707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2929 eq247707
  have eq250425 : (τ (σ y)) = (M.op (τ (σ y)) x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq28 eq250199
    | exact resolve eq250199 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250199
  have eq250537 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq29 eq250425
    | exact resolve eq250425 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250425
  have eq250538 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq250537
  have eq250630 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq46161 x
       have i₂ := eq250538
       grind)
    | exact superpose eq250538 eq46161
    | exact resolve eq46161 eq250538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46161 eq250538
  have eq250789 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq48761 eq250630
    | exact resolve eq250630 eq48761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48761 eq250630
  have eq250813 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq250789
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq250789
    | exact resolve eq250789 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250789
  have eq251457 : ∀ X0 : G, y = (M.op (M.op X0 x) x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq250813 eq146518
    | exact resolve eq146518 eq250813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146518 eq250813
  have eq251653 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq251457 x
       have i₂ := eq29265 x x
       grind)
    | exact superpose eq29265 eq251457
    | exact resolve eq251457 eq29265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29265 eq251457
  have eq252623 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq602 x
       have i₂ := eq251653
       grind)
    | exact superpose eq251653 eq602
    | exact resolve eq602 eq251653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602 eq251653
  have eq252978 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq252623
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq252623
    | exact resolve eq252623 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252623
  have eq253089 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq252978
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq252978
    | exact resolve eq252978 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252978
  have eq253130 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq253089
    | exact resolve eq253089 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253089
  have eq253149 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq253130
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq253130
    | exact resolve eq253130 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253130
  have eq253161 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq253149
    | exact resolve eq253149 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253149
  have eq253162 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq253161
       have r₂ := eq27
       grind)
    | exact resolve eq253161 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253161
  have eq253164 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq253162 eq29
    | exact resolve eq29 eq253162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq253162
  have eq253506 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq253164
    | exact resolve eq253164 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq253164
  have eq253507 : x = y := by grind
  clear eq253506
  have eq253537 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq253507
       grind)
    | exact superpose eq253507 eq18
    | exact resolve eq18 eq253507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq253538 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq253507
       grind)
    | exact superpose eq253507 eq24
    | exact resolve eq24 eq253507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq253507
  have eq254056 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq253538
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq253538
    | exact resolve eq253538 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq253538
  have eq254131 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq254056 eq26
    | exact resolve eq26 eq254056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq254056
  have eq255316 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq254131 eq71
    | exact resolve eq71 eq254131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq254131
  have eq255731 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq255316
       have i₂ := eq253537
       grind)
    | exact superpose eq253537 eq255316
    | exact resolve eq255316 eq253537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253537 eq255316
  have eq255938 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq255731 eq15
    | exact resolve eq15 eq255731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255731
  have eq256296 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq255938
    | exact resolve eq255938 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq255938
  have eq256423 : False := by grind
  exact eq256423

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) ≠ (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq1333 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1337 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) ≠ (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1544 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
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
  have eq1548 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
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
  clear eq19
  have eq1551 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1548 X0 X1
       have j1 := eq1337 X0 X1
       grind)
    | (have r₁ := eq1548 X0 X1
       have r₂ := eq1337 X0 X1
       grind)
    | (have r₁ := eq1548 X0 (τ X0)
       have r₂ := eq1337 X0 (τ X0)
       grind)
    | exact resolve eq1548 eq1337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337 eq1548
  have eq1555 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1544 X0 X1
       have j1 := eq1333 X0 X1
       grind)
    | (have r₁ := eq1544 X0 X1
       have r₂ := eq1333 X0 X1
       grind)
    | (have r₁ := eq1544 X1 X1
       have r₂ := eq1333 X1 X1
       grind)
    | exact resolve eq1544 eq1333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544
  have eq1558 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1551 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1551
    | exact resolve eq1551 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551
  have eq1582 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1558 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1558
    | (have j0 := eq1558 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq1558 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1558
  have eq1754 : ∀ X0 X1 : G, (τ (σ X0)) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq1555 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq1555 X0 X1
       grind)
    | exact superpose eq1555 eq10
    | (have j1 := eq1555 X0 X1
       grind)
    | exact resolve eq10 eq1555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1555
  have eq1776 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1754 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1754
    | (have j0 := eq1754 X0 X1
       grind)
    | exact resolve eq1754 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1754
  have eq1805 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1776 x y
       grind)
    | exact superpose eq1776 eq16
    | (have j1 := eq1776 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1776 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq1776 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq1776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776
  have eq1829 : x = y := by
    first
    | (have j1 := eq1582 x y
       grind)
    | (have r₁ := eq1805
       have r₂ := eq1582 x y
       grind)
    | (have r₁ := eq1805
       have r₂ := eq1582 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1805
       have r₂ := eq1582 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1805 eq1582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1582 eq1805
  have eq1832 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1829
       grind)
    | exact superpose eq1829 eq16
    | exact resolve eq16 eq1829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1829
  have eq3472 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq1333 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1333
  have eq3494 : (σ (M.op x x)) ≠ (σ (k x x)) := by
    first
    | (have i₁ := eq1832
       have i₂ := eq3472 x
       grind)
    | exact superpose eq3472 eq1832
    | exact resolve eq1832 eq3472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1832 eq3472
  have eq3634 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x x) ≠ (M.op x x) := by
    first
    | (have i₁ := eq3494
       have i₂ := eq12 x x
       grind)
    | exact superpose eq12 eq3494
    | (have j1 := eq12 x x
       grind)
    | exact resolve eq3494 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3494
  have eq3637 : False := by grind
  exact eq3637

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pxy_x_pyy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
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
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq33 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X2 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq22
    | exact resolve eq22 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq40
    | exact resolve eq40 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq40 X0 X0
       grind)
    | exact superpose eq40 eq9
    | exact resolve eq9 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X1 X0) = (k (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq9
    | exact resolve eq9 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq40 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq40
    | exact resolve eq40 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq9
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq12
    | (have j0 := eq12 (M.op X0 (M.op X0 X0)) X0
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op X0 X0)) X0
       have r₂ := eq66 X0
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have j0 := eq73 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq86 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq86 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq86
    | (have j0 := eq86 (σ X0)
       grind)
    | exact resolve eq86 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) X0
       have i₂ := eq86 (σ X0)
       grind)
    | exact superpose eq86 eq22
    | (have j1 := eq86 (σ X0)
       grind)
    | exact resolve eq22 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq107 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq106 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq106
    | (have j0 := eq106 X0
       grind)
    | exact resolve eq106 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq111 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 (M.op (M.op x x) (M.op X0 X0)) x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq142 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq153 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq72 X0 X0
       grind)
    | exact superpose eq72 eq72
    | exact resolve eq72 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X1 X1))
       have i₂ := eq72 X1 X0
       grind)
    | exact superpose eq72 eq9
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq72 X0 X0
       grind)
    | exact superpose eq72 eq9
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq111 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq72 X1 X1
       grind)
    | exact superpose eq72 eq111
    | exact resolve eq111 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq168 X2 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq72 X0 X0
       grind)
    | exact superpose eq72 eq168
    | exact resolve eq168 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq317 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 X2
       have i₂ := eq170 X2 X0 X1
       grind)
    | exact superpose eq170 eq66
    | exact resolve eq66 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq318 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X2
       have i₂ := eq170 X2 X0 X1
       grind)
    | exact superpose eq170 eq71
    | exact resolve eq71 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq322 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq176 X2 X3
       have i₂ := eq170 X2 X0 X1
       grind)
    | exact superpose eq170 eq176
    | exact resolve eq176 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X2)) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq168 X2 X3 X2
       have i₂ := eq170 X2 X0 X1
       grind)
    | exact superpose eq170 eq168
    | exact resolve eq168 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X3) X3 X2
       have i₂ := eq170 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq170 eq9
    | exact resolve eq9 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq317 x x (M.op X0 X0)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq317
    | exact resolve eq317 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq385 X0
       grind)
    | exact superpose eq385 eq12
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq385 X0
       grind)
    | exact resolve eq12 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq419 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq409 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq436 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq419 (σ X0)
       grind)
    | exact superpose eq419 eq28
    | exact resolve eq28 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq437 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq419 (τ X0)
       grind)
    | exact superpose eq419 eq17
    | exact resolve eq17 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq419
  have eq438 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq437 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq437
    | exact resolve eq437 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq439 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq436 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq436
    | exact resolve eq436 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq738 : ∀ X0 X1 X2 X3 : G, (σ X0) = (M.op X2 (M.op (M.op X3 X2) (M.op (σ X0) (σ X1)))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (σ X0) X2 X3
       have i₂ := eq142 X0 X1
       grind)
    | (have i₁ := eq9 (σ X1) X1 X2
       have i₂ := eq142 X1 X1
       grind)
    | exact superpose eq142 eq9
    | (have j1 := eq142 X0 X1
       grind)
    | exact resolve eq9 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq759 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq142 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq142 X0 X1
       grind)
    | exact superpose eq142 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq142 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq142 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq142 X1 X1
       grind)
    | exact resolve eq13 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq769 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq759 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq770 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq769 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq773 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq770 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq770
    | (have j0 := eq770 X0 X1
       grind)
    | exact resolve eq770 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq1066 : ∀ X0 X1 : G, (k (σ X1) (k X0 (σ (τ X0)))) = (σ (k X1 (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 (τ X0) X1
       have i₂ := eq86 (τ X0)
       grind)
    | exact superpose eq86 eq20
    | (have j1 := eq86 (τ X0)
       grind)
    | exact resolve eq20 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq86
  have eq1096 : ∀ X0 X1 : G, (σ (k X1 (M.op (τ X0) (τ X0)))) = (k (σ X1) (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1066 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1066
    | (have j0 := eq1066 X0 X1
       grind)
    | exact resolve eq1066 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066
  have eq1309 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X4 X3) (M.op X0 X1))) = (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq69 (M.op X1 (M.op X0 X1)) (M.op X2 (M.op X1 (M.op X0 X1))) X3 X4
       have i₂ := eq69 X1 X0 (M.op X1 (M.op X0 X1)) X2
       grind)
    | exact superpose eq69 eq69
    | exact resolve eq69 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1310 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op X3 (M.op (M.op X4 X3) (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq69 X2 X2 X3 X4
       have i₂ := eq170 X2 X0 X1
       grind)
    | exact superpose eq170 eq69
    | exact resolve eq69 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1311 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq69 X0 (M.op X1 X0) X2 X3
       have i₂ := eq170 X0 X0 X1
       grind)
    | exact superpose eq170 eq69
    | exact resolve eq69 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1322 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq69 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq69 eq69
    | exact resolve eq69 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1384 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1311 X0 X1 x x
       have i₂ := eq69 X0 X0 x x
       grind)
    | exact superpose eq69 eq1311
    | exact resolve eq1311 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311
  have eq1713 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op (M.op X2 X1) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq9
    | (have j1 := eq99 X0
       grind)
    | exact resolve eq9 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq1999 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op (M.op X3 (M.op X3 X3)) (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq153 X2 X3
       have i₂ := eq170 X2 X0 X1
       grind)
    | exact superpose eq170 eq153
    | exact resolve eq153 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq170
  have eq2836 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op (M.op X4 X0) (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq240 (M.op X1 (M.op (M.op X2 X1) X0)) X3 (M.op X4 X0)
       have i₂ := eq322 X1 X2 X0 X4
       grind)
    | exact superpose eq322 eq240
    | exact resolve eq240 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3047 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2836 X0 X1 X2 X3 X4
       have i₂ := eq40 X4 X0
       grind)
    | exact superpose eq40 eq2836
    | exact resolve eq2836 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2836
  have eq3114 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op (M.op X2 X1) X0) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3047 X0 X1 X2 X3 X4
       have i₂ := eq40 X1 (M.op (M.op X2 X1) X0)
       grind)
    | exact superpose eq40 eq3047
    | exact resolve eq3047 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3047
  have eq3142 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3114 X0 X1 X2 X3 X4
       have i₂ := eq322 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq322 eq3114
    | exact resolve eq3114 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3114
  have eq3151 : ∀ X0 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq3142 X0 x x X3 X4
       have i₂ := eq318 x x X0
       grind)
    | exact superpose eq318 eq3142
    | exact resolve eq3142 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318 eq3142
  have eq3181 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3151 (M.op X1 X0) X2 (M.op x (M.op X1 X1))
       have i₂ := eq240 X0 x X1
       grind)
    | exact superpose eq240 eq3151
    | exact resolve eq3151 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3269 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3181 X0 X1 X2
       have i₂ := eq176 X0 X1
       grind)
    | exact superpose eq176 eq3181
    | exact resolve eq3181 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3181
  have eq3291 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3269 X0 X1 X2
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq3269
    | exact resolve eq3269 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3269
  have eq3339 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) ∨ (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) = (k (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 (M.op X1 (M.op X0 X1)) (M.op X2 (M.op X1 (M.op X0 X1)))
       have i₂ := eq69 X1 X0 (M.op X1 (M.op X0 X1)) X2
       grind)
    | exact superpose eq69 eq68
    | (have j0 := eq68 (M.op X1 (M.op X0 X1)) (M.op X2 (M.op X1 (M.op X0 X1)))
       grind)
    | exact resolve eq68 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq3354 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) ∨ (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) = (k (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3339 X0 X1 X2
       have i₂ := eq1384 (M.op X1 (M.op X0 X1)) X2
       grind)
    | exact superpose eq1384 eq3339
    | (have j0 := eq3339 X0 X1 X2
       grind)
    | exact resolve eq3339 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3339
  have eq3375 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) ∨ (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) = (k (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3354 X0 X1 X2
       have i₂ := eq40 X1 (M.op X0 X1)
       grind)
    | exact superpose eq40 eq3354
    | (have j0 := eq3354 X0 X1 X2
       grind)
    | exact resolve eq3354 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3354
  have eq3378 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) = (k (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1)))) ∨ (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3375 X0 X1 X1
       have i₂ := eq1384 (M.op X1 (M.op X0 X1)) X1
       grind)
    | exact superpose eq1384 eq3375
    | (have j0 := eq3375 X0 X1 x
       grind)
    | exact resolve eq3375 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3375
  have eq3381 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (k (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) ∨ (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3378 X0 X0
       have i₂ := eq40 X0 (M.op X0 X0)
       grind)
    | exact superpose eq40 eq3378
    | (have j0 := eq3378 X0 X1
       grind)
    | exact resolve eq3378 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3378
  have eq5256 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X0) = (M.op (M.op X1 (M.op (M.op (M.op X2 (M.op X3 X0)) X0) (M.op (M.op X2 (M.op X3 X0)) X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq323 X0 X3 (M.op (M.op X2 (M.op X3 X0)) X0) X1
       have i₂ := eq317 (M.op X3 X0) X2 X0
       grind)
    | exact superpose eq317 eq323
    | exact resolve eq323 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq5431 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X0) = (M.op (M.op X1 (M.op X0 (M.op (M.op X2 (M.op X3 X0)) X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5256 X0 X1 X2 X3
       have i₂ := eq40 (M.op X2 (M.op X3 X0)) X0
       grind)
    | exact superpose eq40 eq5256
    | exact resolve eq5256 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5256
  have eq5509 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op X3 X0)) X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq5431 X0 x X2 X3
       have i₂ := eq3151 X0 x (M.op X2 (M.op X3 X0))
       grind)
    | exact superpose eq3151 eq5431
    | exact resolve eq5431 eq3151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3151 eq5431
  have eq6547 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq334 X0 X1 X1 X0
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq334
    | exact resolve eq334 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6552 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq334 (M.op X1 X1) x X1 (M.op X0 X0)
       have i₂ := eq168 X1 x X0
       grind)
    | exact superpose eq168 eq334
    | exact resolve eq334 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq6562 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq334 X3 X2 (M.op X1 (M.op X2 X3)) (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq9 eq334
    | exact resolve eq334 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6724 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X0)) = (M.op X0 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6562 X0 X1 X2 X3
       have i₂ := eq3291 X0 X3 X0
       grind)
    | exact superpose eq3291 eq6562
    | exact resolve eq6562 eq3291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6562
  have eq6731 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6552 X0 X1
       have i₂ := eq3291 X0 (M.op X1 X1) X0
       grind)
    | exact superpose eq3291 eq6552
    | exact resolve eq6552 eq3291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6552
  have eq7046 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6731 (M.op X1 X0) (M.op X1 X1)
       have i₂ := eq240 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq240 eq6731
    | exact resolve eq6731 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq7115 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X1 (M.op X1 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6547 X1 (M.op X0 X0)
       have i₂ := eq6731 X1 X0
       grind)
    | exact superpose eq6731 eq6547
    | exact resolve eq6547 eq6731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7177 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X0 X0)) X2) (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq322 (M.op X0 X0) X1 X2 (M.op X1 (M.op X0 X0))
       have i₂ := eq6731 (M.op (M.op X1 (M.op X0 X0)) X2) X0
       grind)
    | exact superpose eq6731 eq322
    | exact resolve eq322 eq6731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7214 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7177 X0 X1 X2
       have i₂ := eq40 (M.op X1 (M.op X0 X0)) X2
       grind)
    | exact superpose eq40 eq7177
    | exact resolve eq7177 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7177
  have eq7274 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7046 X0 X1
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq7046
    | exact resolve eq7046 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7046
  have eq7332 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7274 X0 X1
       have i₂ := eq176 X0 X1
       grind)
    | exact superpose eq176 eq7274
    | exact resolve eq7274 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq7274
  have eq7466 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7332 (M.op (M.op X2 X1) X0) X1
       have i₂ := eq322 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq322 eq7332
    | exact resolve eq7332 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq7473 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6731 (M.op X0 (M.op X1 X0)) X1
       have i₂ := eq7332 X0 X1
       grind)
    | exact superpose eq7332 eq6731
    | exact resolve eq6731 eq7332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7524 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq317 (M.op X0 (M.op X2 X0)) (M.op X2 X2) X1
       have i₂ := eq7332 X0 X2
       grind)
    | exact superpose eq7332 eq317
    | exact resolve eq317 eq7332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7589 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq7473 X0 X1
       have i₂ := eq40 X0 (M.op X1 X0)
       grind)
    | exact superpose eq40 eq7473
    | exact resolve eq7473 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7473
  have eq7652 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq7589 X0 X1
       have i₂ := eq5509 X0 X0 X1
       grind)
    | exact superpose eq5509 eq7589
    | exact resolve eq7589 eq5509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5509 eq7589
  have eq7756 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7466 X2 X1 X0
       have i₂ := eq7466 X2 X1 X3
       grind)
    | (have i₁ := eq7466 X0 X1 X2
       have i₂ := eq7466 X0 X1 X1
       grind)
    | exact superpose eq7466 eq7466
    | exact resolve eq7466 eq7466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7766 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7466 (M.op X0 (M.op X2 X0)) X2 X1
       have i₂ := eq7332 X0 X2
       grind)
    | exact superpose eq7332 eq7466
    | exact resolve eq7466 eq7332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7466
  have eq9480 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq773 (τ X1) (τ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq773
    | (have j0 := eq773 (τ X0) (τ X1)
       grind)
    | exact resolve eq773 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9487 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 (τ X0))) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq773 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq773
    | exact resolve eq773 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq9647 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9487 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq9487
    | (have j0 := eq9487 X0 X1
       grind)
    | exact resolve eq9487 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9487
  have eq9654 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9480 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9480
    | (have j0 := eq9480 X0 X1
       grind)
    | exact resolve eq9480 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9480
  have eq9666 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9647 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq9647
    | (have j0 := eq9647 X0 X1
       grind)
    | exact resolve eq9647 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9647
  have eq9673 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9654 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq9654
    | (have j0 := eq9654 X0 X1
       grind)
    | exact resolve eq9654 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9654
  have eq9684 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9673 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9673
    | (have j0 := eq9673 X0 X1
       grind)
    | exact resolve eq9673 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9673
  have eq9689 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9684 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9684
    | (have j0 := eq9684 X0 X1
       grind)
    | exact resolve eq9684 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9684
  have eq9690 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9689 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9689
    | (have j0 := eq9689 X0 X1
       grind)
    | exact resolve eq9689 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9689
  have eq9691 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9690 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq9690
    | (have j0 := eq9690 X0 X1
       grind)
    | exact resolve eq9690 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9690
  have eq9692 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9691 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq9691
    | (have j0 := eq9691 X0 X1
       grind)
    | exact resolve eq9691 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9691
  have eq10299 : ∀ X0 X1 X2 X3 : G, (σ X1) = (M.op X2 (M.op (M.op X3 X2) (M.op (σ X1) X0))) ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq738 X0 (τ X0) X2 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq738
    | exact resolve eq738 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq10502 : ∀ X0 X1 X2 X3 : G, (σ X1) = (M.op X2 (M.op (M.op X3 X2) (M.op (σ X1) X0))) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10299 X0 X1 X2 X3
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq10299
    | (have j0 := eq10299 X0 X1 X2 X3
       grind)
    | exact resolve eq10299 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10299
  have eq11123 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7524 X2 X3 X1
       have i₂ := eq7756 X2 (M.op X1 X2) (M.op X2 X3) X0
       grind)
    | (have i₁ := eq7524 X2 X3 X1
       have i₂ := eq7756 X0 (M.op X1 X2) (M.op X2 X3) X2
       grind)
    | exact superpose eq7756 eq7524
    | exact resolve eq7524 eq7756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7524
  have eq27181 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq7214 X1 x (M.op X0 X0)
       have i₂ := eq6724 X0 x X1 X1
       grind)
    | exact superpose eq6724 eq7214
    | exact resolve eq7214 eq6724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7214
  have eq29629 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = (M.op (M.op (M.op X2 (M.op X3 X1)) (M.op X2 (M.op X3 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7115 (M.op X2 (M.op X3 X1)) X0
       have i₂ := eq6724 X0 X2 X3 X1
       grind)
    | exact superpose eq6724 eq7115
    | exact resolve eq7115 eq6724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6724 eq7115
  have eq30194 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = (M.op (M.op (M.op X3 X1) (M.op X2 (M.op X3 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq29629 X0 X1 X2 X3
       have i₂ := eq40 X2 (M.op X3 X1)
       grind)
    | exact superpose eq40 eq29629
    | exact resolve eq29629 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29629
  have eq30365 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = (M.op (M.op X1 (M.op X2 (M.op X3 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30194 X0 X1 X2 X3
       have i₂ := eq1322 X2 X3 X1
       grind)
    | exact superpose eq1322 eq30194
    | exact resolve eq30194 eq1322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30194
  have eq30441 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 (M.op X2 (M.op X3 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30365 X0 X1 X2 X3
       have i₂ := eq6547 X0 X1
       grind)
    | exact superpose eq6547 eq30365
    | exact resolve eq30365 eq6547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6547 eq30365
  have eq30705 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq30441 X4 X3 X1 X2
       have i₂ := eq7756 X3 (M.op X1 (M.op X2 X3)) X4 X0
       grind)
    | (have i₁ := eq30441 X4 X3 X1 X2
       have i₂ := eq7756 X0 (M.op X1 (M.op X2 X3)) X4 X3
       grind)
    | exact superpose eq7756 eq30441
    | exact resolve eq30441 eq7756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7756 eq30441
  have eq38328 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq7652 X0 X1
       have i₂ := eq1322 X0 X1 X0
       grind)
    | exact superpose eq1322 eq7652
    | exact resolve eq7652 eq1322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7652
  have eq39737 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op X1 (M.op (M.op X2 X1) (k (σ (τ X0)) X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1713 (τ X0) X1 X2
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1713
    | (have j0 := eq1713 (τ X0) X1 X2
       grind)
    | exact resolve eq1713 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1713
  have eq40041 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (k X0 X0))) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39737 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39737
    | (have j0 := eq39737 X0 X1 X2
       grind)
    | exact resolve eq39737 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39737
  have eq40108 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40041 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq40041
    | (have j0 := eq40041 X0 X1 X2
       grind)
    | exact resolve eq40041 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40041
  have eq45875 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))))) = (k (σ (M.op (M.op (τ X0) (τ X0)) (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))))) (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1096 X0 (M.op (M.op (τ X0) (τ X0)) (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))))
       have i₂ := eq74 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq74 eq1096
    | (have j0 := eq1096 X0 x
       grind)
    | exact resolve eq1096 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq1096
  have eq45969 : ∀ X0 : G, (σ (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))))) = (k (σ (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))))) (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq45875 X0
       have i₂ := eq6731 (M.op (τ X0) (τ X0)) (τ X0)
       grind)
    | exact superpose eq6731 eq45875
    | (have j0 := eq45875 X0
       grind)
    | exact resolve eq45875 eq6731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6731 eq45875
  have eq45976 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq45969 X0
       have i₂ := eq9 (τ X0) (τ X0) (τ X0)
       grind)
    | exact superpose eq9 eq45969
    | (have j0 := eq45969 X0
       grind)
    | exact resolve eq45969 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45969
  have eq45980 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq45976 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45976
    | (have j0 := eq45976 X0
       grind)
    | exact resolve eq45976 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45976
  have eq45982 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ X0) = (k (σ X0) (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq45980 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45980
    | (have j0 := eq45980 (σ X0)
       grind)
    | exact resolve eq45980 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45992 : ∀ X0 : G, (k X0 (σ (τ X0))) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq438 X0
       have i₂ := eq45980 X0
       grind)
    | exact superpose eq45980 eq438
    | (have j1 := eq45980 X0
       grind)
    | exact resolve eq438 eq45980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438 eq45980
  have eq46199 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq45992 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45992
    | (have j0 := eq45992 X0
       grind)
    | exact resolve eq45992 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45992
  have eq46200 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq45982 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq45982
    | (have j0 := eq45982 X0
       grind)
    | exact resolve eq45982 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45982
  have eq46211 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq46200 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq46200
    | (have j0 := eq46200 X0
       grind)
    | exact resolve eq46200 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46200
  have eq46222 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) (k X0 (τ (σ X0)))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0 (σ X0) (σ X0)
       have i₂ := eq46199 (σ X0)
       grind)
    | exact superpose eq46199 eq33
    | (have j1 := eq46199 (σ X0)
       grind)
    | exact resolve eq33 eq46199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq46199
  have eq46265 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq46222 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46222
    | (have j0 := eq46222 X0
       grind)
    | exact resolve eq46222 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46222
  have eq46289 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46265 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq46265
    | (have j0 := eq46265 X0
       grind)
    | exact resolve eq46265 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46265
  have eq46455 : ∀ X0 : G, (τ (σ X0)) = (k X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 (k X0 X0))
       have i₂ := eq46211 X0
       grind)
    | exact superpose eq46211 eq10
    | (have j1 := eq46211 X0
       grind)
    | exact resolve eq10 eq46211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46211
  have eq46552 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq46455 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46455
    | (have j0 := eq46455 X0
       grind)
    | exact resolve eq46455 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46455
  have eq47436 : ∀ X0 X1 X3 X4 : G, (M.op X3 (M.op (M.op X4 X3) (M.op X0 X1))) = (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq1309 X0 X1 x X3 X4
       have i₂ := eq1384 (M.op X1 (M.op X0 X1)) x
       grind)
    | exact superpose eq1384 eq1309
    | exact resolve eq1309 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1309
  have eq47437 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op X3 (M.op (M.op X4 X3) (M.op X0 X1))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq47436 X0 X1 X3 X4
       have i₂ := eq40 X1 (M.op X0 X1)
       grind)
    | exact superpose eq40 eq47436
    | exact resolve eq47436 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47436
  have eq47438 : ∀ X0 X1 X3 X4 : G, (M.op X3 (M.op (M.op X4 X3) (M.op X0 X1))) = (M.op X1 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq47437 X0 X1 X3 X4
       have i₂ := eq1322 X1 X0 X1
       grind)
    | exact superpose eq1322 eq47437
    | exact resolve eq47437 eq1322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47437
  have eq48100 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq38328 X3 X2
       have i₂ := eq47438 X2 X3 X0 X1
       grind)
    | exact superpose eq47438 eq38328
    | exact resolve eq38328 eq47438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38328
  have eq52786 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq9666 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9666
  have eq69246 : ∀ X0 X1 X2 X3 X4 X5 : G, (σ X4) = (M.op (M.op X3 (M.op X2 X3)) (M.op (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3))) (M.op (σ X4) X5))) ∨ (k (σ X4) X5) = (M.op X5 (σ X4)) ∨ (M.op X5 (σ X4)) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq10502 X5 X4 (M.op X3 (M.op X2 X3)) X3
       have i₂ := eq47438 X2 X3 X0 X1
       grind)
    | exact superpose eq47438 eq10502
    | (have j0 := eq10502 X5 X4 X2 X3
       grind)
    | exact resolve eq10502 eq47438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69544 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X4 X3) (σ X0))) = (M.op (M.op X1 (M.op (σ X0) X2)) (M.op (σ X0) X2)) ∨ (M.op X2 (σ X0)) = (k (σ X0) X2) ∨ (M.op X2 (σ X0)) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq69 (M.op (σ X0) X2) (M.op X1 (M.op (σ X0) X2)) X3 X4
       have i₂ := eq10502 X2 X0 (M.op (σ X0) X2) X1
       grind)
    | exact superpose eq10502 eq69
    | (have j1 := eq10502 X2 X0 X2 X3
       grind)
    | exact resolve eq69 eq10502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq10502
  have eq69938 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op (M.op X4 X3) (σ X0))) = (M.op (M.op (σ X0) X2) (M.op (σ X0) X2)) ∨ (M.op X2 (σ X0)) = (k (σ X0) X2) ∨ (M.op X2 (σ X0)) = X2 := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq69544 X0 x X2 X3 X4
       have i₂ := eq1384 (M.op (σ X0) X2) x
       grind)
    | exact superpose eq1384 eq69544
    | (have j0 := eq69544 X0 x X2 X3 X4
       grind)
    | exact resolve eq69544 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69544
  have eq70062 : ∀ X2 X3 X4 X5 : G, (σ X4) = (M.op (M.op X3 (M.op X2 X3)) (M.op X3 (M.op (σ X4) X5))) ∨ (k (σ X4) X5) = (M.op X5 (σ X4)) ∨ (M.op X5 (σ X4)) = X5 := by
    intro X2 X3 X4 X5
    first
    | (have i₁ := eq69246 x x X2 X3 X4 X5
       have i₂ := eq30705 x (M.op x x) X2 X3 (M.op (σ X4) X5)
       grind)
    | exact superpose eq30705 eq69246
    | (have j0 := eq69246 x x X2 X3 X4 X5
       grind)
    | exact resolve eq69246 eq30705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69246
  have eq70128 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op (M.op X4 X3) (σ X0))) = (M.op X2 (M.op (σ X0) X2)) ∨ (M.op X2 (σ X0)) = (k (σ X0) X2) ∨ (M.op X2 (σ X0)) = X2 := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq69938 X0 X2 X3 X4
       have i₂ := eq40 (σ X0) X2
       grind)
    | exact superpose eq40 eq69938
    | (have j0 := eq69938 X0 X2 X3 X4
       grind)
    | exact resolve eq69938 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq69938
  have eq79721 : ∀ X0 X1 X2 X3 : G, (k X3 (τ (M.op X0 (M.op X1 (M.op (M.op X2 X1) (M.op X0 (σ X3))))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq439 X3
       have i₂ := eq48100 X1 X2 X0 (σ X3)
       grind)
    | exact superpose eq48100 eq439
    | exact resolve eq439 eq48100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439 eq48100
  have eq102399 : ∀ X0 X1 X2 X3 : G, (M.op (k X0 X0) X0) = (M.op X1 (M.op (M.op X2 X1) (M.op (M.op X3 (k X0 X0)) (k X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq47438 (M.op X3 (k X0 X0)) (k X0 X0) X1 X2
       have i₂ := eq40108 X0 (k X0 X0) X3
       grind)
    | exact superpose eq40108 eq47438
    | (have j1 := eq40108 X0 X1 X2
       grind)
    | exact resolve eq47438 eq40108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40108 eq47438
  have eq102722 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) X0) = (M.op X1 (M.op (M.op X2 X1) (M.op (k X0 X0) (k X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq102399 X0 X1 X2 x
       have i₂ := eq1384 (k X0 X0) x
       grind)
    | exact superpose eq1384 eq102399
    | (have j0 := eq102399 X0 X1 X2 x
       grind)
    | exact resolve eq102399 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384 eq102399
  have eq102841 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq102722 X0 x x
       have i₂ := eq9 (k X0 X0) x x
       grind)
    | exact superpose eq9 eq102722
    | (have j0 := eq102722 X0 x x
       grind)
    | exact resolve eq102722 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102722
  have eq102902 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (k X0 X0) X1))) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq317 X0 (k X0 X0) X1
       have i₂ := eq102841 X0
       grind)
    | exact superpose eq102841 eq317
    | (have j1 := eq102841 X0
       grind)
    | exact resolve eq317 eq102841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102841
  have eq144697 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 X5) = (M.op X4 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X5)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1310 (M.op X2 (M.op X3 X4)) X1 X5 X4 X3
       have i₂ := eq1999 (M.op X3 X4) X2 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X5) X0
       grind)
    | exact superpose eq1999 eq1310
    | exact resolve eq1310 eq1999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310
  have eq144830 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X2 (M.op (M.op X3 X3) (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq334 (M.op X3 X3) X3 X3 X2
       have i₂ := eq1999 X0 X1 X2 X3
       grind)
    | exact superpose eq1999 eq334
    | exact resolve eq334 eq1999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq1999
  have eq145679 : ∀ X0 X4 X5 : G, (M.op X5 X5) = (M.op X4 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X4 X5)))) := by
    intro X0 X4 X5
    first
    | (have i₁ := eq144697 X0 x x x X4 X5
       have i₂ := eq30705 x x x X4 X5
       grind)
    | exact superpose eq30705 eq144697
    | exact resolve eq144697 eq30705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144697
  have eq213429 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X1))) = (k (M.op X1 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X1 (M.op X0 X1)))) ∨ (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3381 X1 X0
       have i₂ := eq1322 X0 X1 X0
       grind)
    | exact superpose eq1322 eq3381
    | (have j0 := eq3381 X0 X1
       grind)
    | exact resolve eq3381 eq1322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3381
  have eq213430 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X1 (M.op X0 X1))) ∨ (M.op X1 (M.op X1 (M.op X0 X1))) = (k (M.op X1 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq213429 X0 X1
       have i₂ := eq1322 X1 X0 X1
       grind)
    | exact superpose eq1322 eq213429
    | (have j0 := eq213429 X0 X1
       grind)
    | exact resolve eq213429 eq1322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322 eq213429
  have eq213777 : ∀ X0 : G, (M.op (k X0 X0) X0) ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq213430 (k X0 X0) X0
       have i₂ := eq102902 X0 X0
       grind)
    | exact superpose eq102902 eq213430
    | (have j1 := eq102902 X0 x
       grind)
    | exact resolve eq213430 eq102902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102902 eq213430
  have eq213855 : ∀ X0 : G, (M.op (k X0 X0) X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq213777 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq213777 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq213777 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213777
  have eq214806 : ∀ X0 : G, (σ X0) ≠ (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq213855 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq213855
    | exact resolve eq213855 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248830 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X3) = (M.op X4 (M.op (M.op X2 (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X2))))) (M.op X2 (M.op X4 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq145679 X2 X4 X3
       have i₂ := eq145679 X1 X0 X2
       grind)
    | exact superpose eq145679 eq145679
    | exact resolve eq145679 eq145679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145679
  have eq252013 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X3) = (M.op X4 (M.op (M.op X1 (M.op X0 X2)) (M.op X2 (M.op X4 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq248830 X0 X1 X2 X3 X4
       have i₂ := eq30705 X2 X0 (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X2)) (M.op X2 (M.op X4 X3))
       grind)
    | exact superpose eq30705 eq248830
    | exact resolve eq248830 eq30705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30705 eq248830
  have eq798661 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq9692 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9692
  have eq911258 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52786 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq52786
    | exact resolve eq52786 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52786
  have eq2391089 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X2 (σ X0)) (M.op X1 (M.op (σ X0) X1))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq111 X0 (M.op x (M.op (σ x) x))
       have i₂ := eq70062 (σ x) x x x
       grind)
    | exact superpose eq70062 eq111
    | (have j1 := eq70062 X2 x X0 X1
       grind)
    | exact resolve eq111 eq70062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq70062
  have eq2392429 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2391089 X0 X1 x
       have i₂ := eq7766 X1 x (σ X0)
       grind)
    | exact superpose eq7766 eq2391089
    | (have j0 := eq2391089 X0 X1 x
       grind)
    | exact resolve eq2391089 eq7766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2391089
  have eq2395585 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2392429 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2392429
    | exact resolve eq2392429 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2392429
  have eq2397339 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (k X0 X0) = X0 ∨ (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2395585 X0 (k X0 X0)
       have i₂ := eq46552 X0
       grind)
    | exact superpose eq46552 eq2395585
    | (have j0 := eq2395585 (M.op (k X0 X0) X0) X0
       have j1 := eq46552 X0
       grind)
    | exact resolve eq2395585 eq46552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46552 eq2395585
  have eq2399037 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (k X0 X0) = X0 ∨ (k X0 X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq2397339 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq2397339 X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq2397339 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq2397339 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2397339
  have eq2399110 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2399037 X0
       have j1 := eq213855 X0
       grind)
    | (have r₁ := eq2399037 X0
       have r₂ := eq213855 X0
       grind)
    | exact resolve eq2399037 eq213855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213855 eq2399037
  have eq2399407 : ∀ X0 : G, (M.op (M.op (k X0 X0) (k X0 X0)) (M.op X0 (k X0 X0))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7332 X0 (k X0 X0)
       have i₂ := eq2399110 X0
       grind)
    | exact superpose eq2399110 eq7332
    | (have j1 := eq2399110 X0
       grind)
    | exact resolve eq7332 eq2399110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7332
  have eq2400306 : ∀ X0 : G, (M.op (k X0 X0) (M.op X0 (k X0 X0))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2399407 X0
       have i₂ := eq3291 (k X0 X0) X0 (k X0 X0)
       grind)
    | exact superpose eq3291 eq2399407
    | (have j0 := eq2399407 X0
       grind)
    | exact resolve eq2399407 eq3291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3291 eq2399407
  have eq2406027 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op (σ X2) (M.op (M.op X3 X3) (M.op X0 (M.op (M.op X1 X0) (σ X2))))) ∨ (k (σ X2) X3) = (M.op X3 (σ X2)) ∨ (M.op X3 (σ X2)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq27181 X3 (σ X2)
       have i₂ := eq70128 X2 X3 X0 X1
       grind)
    | exact superpose eq70128 eq27181
    | (have j1 := eq70128 X2 X3 X3 x
       grind)
    | exact resolve eq27181 eq70128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27181 eq70128
  have eq2407907 : ∀ X2 X3 : G, (M.op X3 X3) = (M.op X3 (σ X2)) ∨ (k (σ X2) X3) = (M.op X3 (σ X2)) ∨ (M.op X3 (σ X2)) = X3 := by
    intro X2 X3
    first
    | (have i₁ := eq2406027 x x X2 X3
       have i₂ := eq144830 x x (σ X2) X3
       grind)
    | exact superpose eq144830 eq2406027
    | (have j0 := eq2406027 x x X2 X3
       grind)
    | exact resolve eq2406027 eq144830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144830 eq2406027
  have eq2409489 : ∀ X2 X3 : G, (k (σ X2) X3) = (M.op X3 (σ X2)) ∨ (M.op X3 (σ X2)) = X3 := by
    intro X2 X3
    first
    | (have j0 := eq2407907 X2 X3
       have j1 := eq798661 (σ X2) X3
       grind)
    | (have r₁ := eq2407907 X2 (σ X2)
       have r₂ := eq798661 (σ X2) (σ X2)
       grind)
    | (have r₁ := eq2407907 X2 x
       have r₂ := eq798661 (σ X2) x
       grind)
    | exact resolve eq2407907 eq798661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798661 eq2407907
  have eq2416414 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2409489 (τ X0) x
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2409489
    | exact resolve eq2409489 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2416545 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2409489 X0 (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2409489
    | (have j0 := eq2409489 X0 (σ X1)
       grind)
    | exact resolve eq2409489 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2409489
  have eq2684695 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2416545 y x
       grind)
    | exact superpose eq2416545 eq16
    | (have j1 := eq2416545 y x
       grind)
    | exact resolve eq16 eq2416545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2685706 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2416545 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2689022 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2685706 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq2685706
    | (have j0 := eq2685706 (τ X1) (τ X0)
       grind)
    | exact resolve eq2685706 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2689370 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2689022 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2689022
    | (have j0 := eq2689022 X0 X1
       grind)
    | exact resolve eq2689022 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2689022
  have eq2689473 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2689370 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2689370
    | (have j0 := eq2689370 X0 X1
       grind)
    | exact resolve eq2689370 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2689370
  have eq2689532 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2689473 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2689473
    | (have j0 := eq2689473 X0 X1
       grind)
    | exact resolve eq2689473 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2689473
  have eq2689576 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2689532 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2689532
    | (have j0 := eq2689532 X0 X1
       grind)
    | exact resolve eq2689532 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2689532
  have eq2689651 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k X0 X0) = (M.op (k X0 X0) X0) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2689576 X0 (k X0 X0)
       have i₂ := eq46289 X0
       grind)
    | exact superpose eq46289 eq2689576
    | (have j0 := eq2689576 X0 X0
       have j1 := eq46289 X0
       grind)
    | exact resolve eq2689576 eq46289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46289
  have eq2689954 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2689651 X0
       have j1 := eq2399110 X0
       grind)
    | (have r₁ := eq2689651 X0
       have r₂ := eq2399110 X0
       grind)
    | exact resolve eq2689651 eq2399110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2399110 eq2689651
  have eq2791590 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2684695
       have i₂ := eq2416414 y x
       grind)
    | exact superpose eq2416414 eq2684695
    | (have j1 := eq2416414 (σ y) (σ x)
       grind)
    | exact resolve eq2684695 eq2416414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2684695
  have eq2791595 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2791590
  have eq2791616 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2791595
       grind)
    | exact superpose eq2791595 eq16
    | exact resolve eq16 eq2791595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2791728 : ∀ X0 X1 : G, y = (k y (τ (M.op (σ x) (M.op X0 (M.op (M.op X1 X0) (σ x)))))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq79721 (σ x) X0 X1 y
       have i₂ := eq2791595
       grind)
    | exact superpose eq2791595 eq79721
    | exact resolve eq79721 eq2791595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79721
  have eq2792179 : ∀ X0 X1 X2 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op X0 (M.op X1 X2)) (M.op X2 (σ x)))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq252013 X1 X0 X2 (σ y) (σ x)
       have i₂ := eq2791595
       grind)
    | exact superpose eq2791595 eq252013
    | exact resolve eq252013 eq2791595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2791595
  have eq2792333 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2792179 x x x
       have i₂ := eq11123 x x x (σ x)
       grind)
    | exact superpose eq11123 eq2792179
    | exact resolve eq2792179 eq11123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2792179
  have eq2792489 : y = (k y (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2791728 x x
       have i₂ := eq317 x x (σ x)
       grind)
    | exact superpose eq317 eq2791728
    | exact resolve eq2791728 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317 eq2791728
  have eq2792583 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2792489
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2792489
    | exact resolve eq2792489 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2792489
  have eq2792602 : y = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq2792583
       have r₂ := eq12 y x
       grind)
    | exact resolve eq2792583 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2792583
  have eq2792608 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2792602
       have i₂ := eq2416414 y x
       grind)
    | exact superpose eq2416414 eq2792602
    | (have j1 := eq2416414 y x
       grind)
    | exact resolve eq2792602 eq2416414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2416414
  have eq2792691 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2685706 x y
       have i₂ := eq2792602
       grind)
    | exact superpose eq2792602 eq2685706
    | (have j0 := eq2685706 x y
       grind)
    | exact resolve eq2685706 eq2792602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2685706
  have eq2792692 : x ≠ y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2689576 y x
       have i₂ := eq2792602
       grind)
    | exact superpose eq2792602 eq2689576
    | (have j0 := eq2689576 y x
       grind)
    | exact resolve eq2689576 eq2792602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2689576
  have eq2793363 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2791616
       have i₂ := eq2792608
       grind)
    | exact superpose eq2792608 eq2791616
    | exact resolve eq2791616 eq2792608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2791616 eq2792608
  have eq2793364 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2793363
       have r₂ := eq2792692
       grind)
    | exact resolve eq2793363 eq2792692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2792692 eq2793363
  have eq2795504 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq107 y
       have i₂ := eq2792333
       grind)
    | exact superpose eq2792333 eq107
    | exact resolve eq107 eq2792333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq2792333
  have eq2797075 : (k y y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2795504
       have r₂ := eq2793364
       grind)
    | exact resolve eq2795504 eq2793364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2795504
  have eq2797255 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2797075
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2797075
    | exact resolve eq2797075 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2797075
  have eq2797664 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2689954 y
       have i₂ := eq2797255
       grind)
    | exact superpose eq2797255 eq2689954
    | exact resolve eq2689954 eq2797255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2689954 eq2797255
  have eq2797775 : x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq2797664
  have eq2797786 : x = (M.op x y) := by
    first
    | (have r₁ := eq2797775
       have r₂ := eq2793364
       grind)
    | exact resolve eq2797775 eq2793364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2793364 eq2797775
  have eq2798056 : ∀ X0 : G, (M.op x (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq7766 X0 x y
       have i₂ := eq2797786
       grind)
    | exact superpose eq2797786 eq7766
    | exact resolve eq7766 eq2797786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7766
  have eq2798376 : ∀ X0 X1 X2 : G, (M.op y y) = (M.op x (M.op (M.op X0 (M.op X1 X2)) (M.op X2 x))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq252013 X1 X0 X2 y x
       have i₂ := eq2797786
       grind)
    | exact superpose eq2797786 eq252013
    | exact resolve eq252013 eq2797786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252013
  have eq2798495 : x = (M.op y y) := by
    first
    | (have i₁ := eq2798376 x x x
       have i₂ := eq11123 x x x x
       grind)
    | exact superpose eq11123 eq2798376
    | exact resolve eq2798376 eq11123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11123 eq2798376
  have eq2799561 : x ≠ x ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq911258 y y
       have i₂ := eq2798495
       grind)
    | exact superpose eq2798495 eq911258
    | exact resolve eq911258 eq2798495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911258 eq2798495
  have eq2799610 : x = (k y y) ∨ x = y := by grind
  clear eq2799561
  have eq2816303 : (M.op x y) = (k y y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq2798056 (k y y)
       have i₂ := eq2400306 y
       grind)
    | exact superpose eq2400306 eq2798056
    | (have j1 := eq2400306 y
       grind)
    | exact resolve eq2798056 eq2400306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2400306 eq2798056
  have eq2817562 : y = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq2816303
       have i₂ := eq2797786
       grind)
    | exact superpose eq2797786 eq2816303
    | exact resolve eq2816303 eq2797786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2816303
  have eq2933316 : x ≠ y ∨ x = (k y y) := by grind
  clear eq2817562
  have eq2933399 : x = (k y y) := by
    first
    | (have r₁ := eq2933316
       have r₂ := eq2799610
       grind)
    | exact resolve eq2933316 eq2799610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2799610 eq2933316
  have eq2933932 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq214806 y
       have i₂ := eq2933399
       grind)
    | exact superpose eq2933399 eq214806
    | exact resolve eq214806 eq2933399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214806 eq2933399
  have eq3507550 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2933932
       have i₂ := eq2416545 y x
       grind)
    | exact superpose eq2416545 eq2933932
    | (have j1 := eq2416545 y x
       grind)
    | exact resolve eq2933932 eq2416545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2416545 eq2933932
  have eq3507551 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3507550
       have r₂ := eq2792691
       grind)
    | exact resolve eq3507550 eq2792691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2792691 eq3507550
  have eq3507563 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3507551
       have i₂ := eq2792602
       grind)
    | exact superpose eq2792602 eq3507551
    | exact resolve eq3507551 eq2792602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2792602 eq3507551
  have eq3507564 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3507563
  have eq3507600 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3507564
       grind)
    | exact superpose eq3507564 eq16
    | exact resolve eq16 eq3507564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3507564
  have eq3508558 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq3507600
       have i₂ := eq2797786
       grind)
    | exact superpose eq2797786 eq3507600
    | exact resolve eq3507600 eq2797786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2797786 eq3507600
  have eq3508559 : False := by grind
  exact eq3508559

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyx_pyx_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq22 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq22 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq27 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
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
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq40 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq37 (k X0 X0) X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq37 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq38 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq38 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq28 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq28 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq28 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq39 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq39 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq39 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       have j1 := eq40 X1 X0
       grind)
    | (have r₁ := eq43 X1 X0
       have r₂ := eq40 X0 X1
       grind)
    | (have r₁ := eq43 X0 (M.op X1 X1)
       have r₂ := eq40 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq43 X1 X1
       have r₂ := eq40 (k X1 X1) X1
       grind)
    | exact resolve eq43 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq43
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq48
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq52 X0 X1
       grind)
    | (have r₁ := eq53 X0 X1
       have r₂ := eq52 X0 X1
       grind)
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq53
  have eq124 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq128 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq124 X0 X1
       have j1 := eq55 X1 X0
       grind)
    | (have r₁ := eq124 X1 X1
       have r₂ := eq55 X1 X1
       grind)
    | (have r₁ := eq124 X1 X0
       have r₂ := eq55 X0 X1
       grind)
    | exact resolve eq124 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq124
  have eq272 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq128 (σ X1) (σ X0)
       grind)
    | exact superpose eq128 eq15
    | exact resolve eq15 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq272 X0 X1
       have i₂ := eq128 X1 X0
       grind)
    | exact superpose eq128 eq272
    | exact resolve eq272 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq272
  have eq281 : False := by grind
  exact eq281

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pyx_pxy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq63 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq63 X0 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq74 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq9
    | exact resolve eq9 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq296 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X2
       have i₂ := eq142 X2 X0 X1
       grind)
    | exact superpose eq142 eq67
    | exact resolve eq67 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq142
  have eq366 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq296 x x (M.op X0 X0)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq296
    | exact resolve eq296 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq922 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq366 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq366 X0
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq366
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq366 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq947 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq922 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq972 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq947 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq947 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq947 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq1025 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq972 (σ X0) (σ X1)
       grind)
    | exact superpose eq972 eq15
    | exact resolve eq15 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1036 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1025 X0 X1
       have i₂ := eq972 X0 X1
       grind)
    | exact superpose eq972 eq1025
    | exact resolve eq1025 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972 eq1025
  have eq1235 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1036 x y
       grind)
    | exact superpose eq1036 eq16
    | (have r₁ := eq16
       have r₂ := eq1036 x y
       grind)
    | exact resolve eq16 eq1036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq1273 : False := by grind
  exact eq1273

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_x_pxy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq40 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq40
    | exact resolve eq40 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq40 X0 X0
       grind)
    | exact superpose eq40 eq9
    | exact resolve eq9 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X1 X0) = (k (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq9
    | exact resolve eq9 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq40 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq40
    | exact resolve eq40 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq9
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq86 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq86
    | (have j0 := eq86 (σ X0)
       grind)
    | exact resolve eq86 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) X0
       have i₂ := eq86 (σ X0)
       grind)
    | exact superpose eq86 eq22
    | (have j1 := eq86 (σ X0)
       grind)
    | exact resolve eq22 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq103 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq102
    | (have j0 := eq102 X0
       grind)
    | exact resolve eq102 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq107 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 (M.op (M.op x x) (M.op X0 X0)) x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq142 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq169 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X1 X1))
       have i₂ := eq72 X1 X0
       grind)
    | exact superpose eq72 eq9
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq72 X0 X0
       grind)
    | exact superpose eq72 eq9
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq107 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq72 X1 X1
       grind)
    | exact superpose eq72 eq107
    | exact resolve eq107 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq235 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq169 X2 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq72 X0 X0
       grind)
    | exact superpose eq72 eq169
    | exact resolve eq169 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq310 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 X2
       have i₂ := eq171 X2 X0 X1
       grind)
    | exact superpose eq171 eq66
    | exact resolve eq66 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X2
       have i₂ := eq171 X2 X0 X1
       grind)
    | exact superpose eq171 eq71
    | exact resolve eq71 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq315 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq176 X2 X3
       have i₂ := eq171 X2 X0 X1
       grind)
    | exact superpose eq171 eq176
    | exact resolve eq176 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq316 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X2)) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq169 X2 X3 X2
       have i₂ := eq171 X2 X0 X1
       grind)
    | exact superpose eq171 eq169
    | exact resolve eq169 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq326 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X3) X3 X2
       have i₂ := eq171 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq171 eq9
    | exact resolve eq9 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq728 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq142 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq142 X0 X1
       grind)
    | exact superpose eq142 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq142 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq142 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq142 X0 X1
       grind)
    | exact resolve eq13 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq740 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq728 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq741 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq740 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq746 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq741 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq741
    | (have j0 := eq741 X0 X1
       grind)
    | exact resolve eq741 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq747 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq746 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq1267 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X4 X3) (M.op X0 X1))) = (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq69 (M.op X1 (M.op X0 X1)) (M.op X2 (M.op X1 (M.op X0 X1))) X3 X4
       have i₂ := eq69 X1 X0 (M.op X1 (M.op X0 X1)) X2
       grind)
    | exact superpose eq69 eq69
    | exact resolve eq69 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1269 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq69 X0 (M.op X1 X0) X2 X3
       have i₂ := eq171 X0 X0 X1
       grind)
    | exact superpose eq171 eq69
    | exact resolve eq69 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq1280 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq69 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq69 eq69
    | exact resolve eq69 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1340 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1269 X0 X1 x x
       have i₂ := eq69 X0 X0 x x
       grind)
    | exact superpose eq69 eq1269
    | exact resolve eq1269 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1269
  have eq1705 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (k X0 X0)) (M.op X1 X1))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq9
    | (have j1 := eq95 X0
       grind)
    | exact resolve eq9 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1728 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq66 (σ X0)
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq66
    | (have j1 := eq95 X0
       grind)
    | exact resolve eq66 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq2752 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op (M.op X4 X0) (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq235 (M.op X1 (M.op (M.op X2 X1) X0)) X3 (M.op X4 X0)
       have i₂ := eq315 X1 X2 X0 X4
       grind)
    | exact superpose eq315 eq235
    | exact resolve eq235 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2956 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2752 X0 X1 X2 X3 X4
       have i₂ := eq40 X4 X0
       grind)
    | exact superpose eq40 eq2752
    | exact resolve eq2752 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2752
  have eq3018 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op (M.op X2 X1) X0) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2956 X0 X1 X2 X3 X4
       have i₂ := eq40 X1 (M.op (M.op X2 X1) X0)
       grind)
    | exact superpose eq40 eq2956
    | exact resolve eq2956 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2956
  have eq3046 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3018 X0 X1 X2 X3 X4
       have i₂ := eq315 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq315 eq3018
    | exact resolve eq3018 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3018
  have eq3055 : ∀ X0 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq3046 X0 x x X3 X4
       have i₂ := eq311 x x X0
       grind)
    | exact superpose eq311 eq3046
    | exact resolve eq3046 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311 eq3046
  have eq3085 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3055 (M.op X1 X0) X2 (M.op x (M.op X1 X1))
       have i₂ := eq235 X0 x X1
       grind)
    | exact superpose eq235 eq3055
    | exact resolve eq3055 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3175 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3085 X0 X1 X2
       have i₂ := eq176 X0 X1
       grind)
    | exact superpose eq176 eq3085
    | exact resolve eq3085 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3085
  have eq3197 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3175 X0 X1 X2
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq3175
    | exact resolve eq3175 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3175
  have eq3212 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq747 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq747
    | exact resolve eq747 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3232 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq747 x y
       grind)
    | exact superpose eq747 eq16
    | (have j1 := eq747 x y
       grind)
    | exact resolve eq16 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3291 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq747 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3304 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3212 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq3212
    | (have j0 := eq3212 X0 X1
       grind)
    | exact resolve eq3212 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3212
  have eq4253 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) ∨ (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) = (k (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 (M.op X1 (M.op X0 X1)) (M.op X2 (M.op X1 (M.op X0 X1)))
       have i₂ := eq69 X1 X0 (M.op X1 (M.op X0 X1)) X2
       grind)
    | exact superpose eq69 eq68
    | (have j0 := eq68 (M.op X1 (M.op X0 X1)) (M.op X2 (M.op X1 (M.op X0 X1)))
       grind)
    | exact resolve eq68 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq4268 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) ∨ (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) = (k (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4253 X0 X1 X2
       have i₂ := eq1340 (M.op X1 (M.op X0 X1)) X2
       grind)
    | exact superpose eq1340 eq4253
    | (have j0 := eq4253 X0 X1 X2
       grind)
    | exact resolve eq4253 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4253
  have eq4292 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) ∨ (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) = (k (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1))) (M.op (M.op X2 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4268 X0 X1 X2
       have i₂ := eq40 X1 (M.op X0 X1)
       grind)
    | exact superpose eq40 eq4268
    | (have j0 := eq4268 X0 X1 X2
       grind)
    | exact resolve eq4268 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4268
  have eq4295 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) = (k (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1)))) ∨ (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4292 X0 X1 X1
       have i₂ := eq1340 (M.op X1 (M.op X0 X1)) X1
       grind)
    | exact superpose eq1340 eq4292
    | (have j0 := eq4292 X0 X1 x
       grind)
    | exact resolve eq4292 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4292
  have eq4298 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (k (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1)))) ∨ (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4295 X0 X0
       have i₂ := eq40 X0 (M.op X0 X0)
       grind)
    | exact superpose eq40 eq4295
    | (have j0 := eq4295 X0 X1
       grind)
    | exact resolve eq4295 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4295
  have eq4440 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3291 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq3291
    | (have j0 := eq3291 (τ X1) (τ X0)
       grind)
    | exact resolve eq3291 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq4454 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4440 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq4440
    | (have j0 := eq4440 X0 X1
       grind)
    | exact resolve eq4440 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4440
  have eq4461 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4454 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4454
    | (have j0 := eq4454 X0 X1
       grind)
    | exact resolve eq4454 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4454
  have eq4465 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4461 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4461
    | (have j0 := eq4461 X0 X1
       grind)
    | exact resolve eq4461 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4461
  have eq4466 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4465 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4465
    | (have j0 := eq4465 X0 X1
       grind)
    | exact resolve eq4465 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4465
  have eq4484 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3304 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3304
    | exact resolve eq3304 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3304
  have eq5468 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X0) = (M.op (M.op X1 (M.op (M.op (M.op X2 (M.op X3 X0)) X0) (M.op (M.op X2 (M.op X3 X0)) X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq316 X0 X3 (M.op (M.op X2 (M.op X3 X0)) X0) X1
       have i₂ := eq310 (M.op X3 X0) X2 X0
       grind)
    | exact superpose eq310 eq316
    | exact resolve eq316 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq5639 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X0) = (M.op (M.op X1 (M.op X0 (M.op (M.op X2 (M.op X3 X0)) X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5468 X0 X1 X2 X3
       have i₂ := eq40 (M.op X2 (M.op X3 X0)) X0
       grind)
    | exact superpose eq40 eq5468
    | exact resolve eq5468 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5468
  have eq5714 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op X3 X0)) X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq5639 X0 x X2 X3
       have i₂ := eq3055 X0 x (M.op X2 (M.op X3 X0))
       grind)
    | exact superpose eq3055 eq5639
    | exact resolve eq5639 eq3055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3055 eq5639
  have eq6600 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq326 (M.op X1 X1) x X1 (M.op X0 X0)
       have i₂ := eq169 X1 x X0
       grind)
    | exact superpose eq169 eq326
    | exact resolve eq326 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169 eq326
  have eq6773 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6600 X0 X1
       have i₂ := eq3197 X0 (M.op X1 X1) X0
       grind)
    | exact superpose eq3197 eq6600
    | exact resolve eq6600 eq3197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3197 eq6600
  have eq7071 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6773 (M.op X1 X0) (M.op X1 X1)
       have i₂ := eq235 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq235 eq6773
    | exact resolve eq6773 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq7293 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7071 X0 X1
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq7071
    | exact resolve eq7071 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7071
  have eq7348 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7293 X0 X1
       have i₂ := eq176 X0 X1
       grind)
    | exact superpose eq176 eq7293
    | exact resolve eq7293 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq7293
  have eq7477 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7348 (M.op (M.op X2 X1) X0) X1
       have i₂ := eq315 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq315 eq7348
    | exact resolve eq7348 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq7484 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6773 (M.op X0 (M.op X1 X0)) X1
       have i₂ := eq7348 X0 X1
       grind)
    | exact superpose eq7348 eq6773
    | exact resolve eq6773 eq7348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6773
  have eq7595 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq7484 X0 X1
       have i₂ := eq40 X0 (M.op X1 X0)
       grind)
    | exact superpose eq40 eq7484
    | exact resolve eq7484 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7484
  have eq7657 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq7595 X0 X1
       have i₂ := eq5714 X0 X0 X1
       grind)
    | exact superpose eq5714 eq7595
    | exact resolve eq7595 eq5714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5714 eq7595
  have eq7761 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7477 X2 X1 X0
       have i₂ := eq7477 X2 X1 X3
       grind)
    | (have i₁ := eq7477 X0 X1 X2
       have i₂ := eq7477 X0 X1 X1
       grind)
    | exact superpose eq7477 eq7477
    | exact resolve eq7477 eq7477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7477
  have eq18235 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3232
       have i₂ := eq4484 y x
       grind)
    | exact superpose eq4484 eq3232
    | (have j1 := eq4484 (σ y) (σ x)
       grind)
    | exact resolve eq3232 eq4484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3232
  have eq18238 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18235
  have eq18240 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18238
       grind)
    | exact superpose eq18238 eq16
    | exact resolve eq16 eq18238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18243 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq18238
       grind)
    | exact superpose eq18238 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq18238
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq18238
       grind)
    | exact resolve eq12 eq18238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18305 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq18243
  have eq18323 : (σ y) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18305
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq18305
    | exact resolve eq18305 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18305
  have eq18329 : (k y x) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq18323
       grind)
    | exact superpose eq18323 eq10
    | exact resolve eq10 eq18323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18323
  have eq18358 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18329
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq18329
    | exact resolve eq18329 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18329
  have eq18359 : y = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq18358
       have r₂ := eq12 y x
       grind)
    | exact resolve eq18358 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18358
  have eq18360 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18359
       have i₂ := eq4484 y x
       grind)
    | exact superpose eq4484 eq18359
    | (have j1 := eq4484 y x
       grind)
    | exact resolve eq18359 eq4484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4484
  have eq18364 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3291 x y
       have i₂ := eq18359
       grind)
    | exact superpose eq18359 eq3291
    | (have j0 := eq3291 x y
       grind)
    | exact resolve eq3291 eq18359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3291
  have eq18365 : x ≠ y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4466 y x
       have i₂ := eq18359
       grind)
    | exact superpose eq18359 eq4466
    | (have j0 := eq4466 y x
       grind)
    | exact resolve eq4466 eq18359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4466
  have eq18368 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18240
       have i₂ := eq18360
       grind)
    | exact superpose eq18360 eq18240
    | exact resolve eq18240 eq18360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18240
  have eq18410 : y = (M.op (M.op x x) (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7348 y x
       have i₂ := eq18360
       grind)
    | exact superpose eq18360 eq7348
    | exact resolve eq7348 eq18360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7348 eq18360
  have eq18434 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18368
       have r₂ := eq18365
       grind)
    | exact resolve eq18368 eq18365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18368
  have eq33709 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ X1) (M.op (σ (k X1 X1)) X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1705 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq72 X0 X0
       grind)
    | exact superpose eq72 eq1705
    | (have j0 := eq1705 X1 X1
       grind)
    | exact resolve eq1705 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq1705
  have eq36876 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (M.op (σ (τ X0)) (k X0 (σ (τ X0))))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1728 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq1728
    | (have j0 := eq1728 (τ X0)
       grind)
    | exact resolve eq1728 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1728
  have eq37023 : ∀ X0 : G, (M.op X0 (M.op X0 (k X0 X0))) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq36876 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq36876
    | (have j0 := eq36876 X0
       grind)
    | exact resolve eq36876 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36876
  have eq37050 : ∀ X0 : G, (M.op X0 (M.op X0 (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37023 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37023
    | (have j0 := eq37023 X0
       grind)
    | exact resolve eq37023 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37023
  have eq37107 : ∀ X0 : G, (M.op (M.op X0 (k X0 X0)) X0) ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq68 (M.op X0 (k X0 X0)) X0
       have i₂ := eq37050 X0
       grind)
    | exact superpose eq37050 eq68
    | (have j1 := eq37050 X0
       grind)
    | exact resolve eq68 eq37050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq37050
  have eq37281 : ∀ X0 : G, (M.op (M.op X0 (k X0 X0)) X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq37107 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq37107 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq37107 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37107
  have eq37376 : ∀ X0 X1 : G, (M.op (M.op X0 (k X1 X1)) X1) ≠ X1 ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37281 X1
       have i₂ := eq7761 X1 (k X1 X1) X1 X0
       grind)
    | (have i₁ := eq37281 X1
       have i₂ := eq7761 X0 (k X1 X1) X1 X1
       grind)
    | exact superpose eq7761 eq37281
    | (have j0 := eq37281 X1
       grind)
    | exact resolve eq37281 eq7761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7761 eq37281
  have eq39232 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq7657 X0 X1
       have i₂ := eq1280 X0 X1 X0
       grind)
    | exact superpose eq1280 eq7657
    | exact resolve eq7657 eq1280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7657
  have eq41825 : ∀ X0 X1 X3 X4 : G, (M.op X3 (M.op (M.op X4 X3) (M.op X0 X1))) = (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq1267 X0 X1 x X3 X4
       have i₂ := eq1340 (M.op X1 (M.op X0 X1)) x
       grind)
    | exact superpose eq1340 eq1267
    | exact resolve eq1267 eq1340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267
  have eq41826 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op X3 (M.op (M.op X4 X3) (M.op X0 X1))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq41825 X0 X1 X3 X4
       have i₂ := eq40 X1 (M.op X0 X1)
       grind)
    | exact superpose eq40 eq41825
    | exact resolve eq41825 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq41825
  have eq41827 : ∀ X0 X1 X3 X4 : G, (M.op X3 (M.op (M.op X4 X3) (M.op X0 X1))) = (M.op X1 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq41826 X0 X1 X3 X4
       have i₂ := eq1280 X1 X0 X1
       grind)
    | exact superpose eq1280 eq41826
    | exact resolve eq41826 eq1280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41826
  have eq42453 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq39232 X3 X2
       have i₂ := eq41827 X2 X3 X0 X1
       grind)
    | exact superpose eq41827 eq39232
    | exact resolve eq39232 eq41827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39232 eq41827
  have eq68683 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op X0 (M.op (M.op X1 X0) (σ x)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq42453 X0 X1 (σ x) (σ y)
       have i₂ := eq18238
       grind)
    | exact superpose eq18238 eq42453
    | exact resolve eq42453 eq18238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18238
  have eq69976 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq68683 x x
       have i₂ := eq310 x x (σ x)
       grind)
    | exact superpose eq310 eq68683
    | exact resolve eq68683 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68683
  have eq70521 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq103 y
       have i₂ := eq69976
       grind)
    | exact superpose eq69976 eq103
    | exact resolve eq103 eq69976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq69976
  have eq70783 : (k y y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq70521
       have r₂ := eq18434
       grind)
    | exact resolve eq70521 eq18434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18434 eq70521
  have eq70788 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq70783
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq70783
    | exact resolve eq70783 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70783
  have eq70789 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq70788
       have i₂ := eq86 y
       grind)
    | exact superpose eq86 eq70788
    | (have j1 := eq86 y
       grind)
    | exact resolve eq70788 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq70808 : ∀ X0 : G, y ≠ (M.op (M.op X0 x) y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq37376 X0 y
       have i₂ := eq70788
       grind)
    | exact superpose eq70788 eq37376
    | exact resolve eq37376 eq70788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37376 eq70788
  have eq70829 : ∀ X0 : G, y ≠ (M.op (M.op X0 x) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq70808 X0
       grind)
    | (have r₁ := eq70808 X0
       have r₂ := eq18365
       grind)
    | exact resolve eq70808 eq18365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18365 eq70808
  have eq92306 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X1))) = (k (M.op X1 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X1 (M.op X0 X1)))) ∨ (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4298 X1 X0
       have i₂ := eq1280 X0 X1 X0
       grind)
    | exact superpose eq1280 eq4298
    | (have j0 := eq4298 X0 X1
       grind)
    | exact resolve eq4298 eq1280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4298
  have eq92307 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X1 (M.op X0 X1))) ∨ (M.op X1 (M.op X1 (M.op X0 X1))) = (k (M.op X1 (M.op X1 (M.op X0 X1))) (M.op X1 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq92306 X0 X1
       have i₂ := eq1280 X1 X0 X1
       grind)
    | exact superpose eq1280 eq92306
    | (have j0 := eq92306 X0 X1
       grind)
    | exact resolve eq92306 eq1280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280 eq92306
  have eq93430 : y = (M.op (M.op x x) y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18410
       have i₂ := eq70789
       grind)
    | exact superpose eq70789 eq18410
    | exact resolve eq18410 eq70789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18410 eq70789
  have eq93643 : y = (M.op (M.op x x) y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq93430
  have eq93688 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq93643
       have r₂ := eq70829 x
       grind)
    | exact resolve eq93643 eq70829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70829 eq93643
  have eq93824 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1340 y y
       have i₂ := eq93688
       grind)
    | exact superpose eq93688 eq1340
    | exact resolve eq1340 eq93688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340 eq93688
  have eq93916 : x = (M.op x y) := by grind
  clear eq93824
  have eq94115 : ∀ X0 X1 : G, (M.op y y) = (M.op x (M.op X0 (M.op (M.op X1 X0) x))) := by
    intro X0 X1
    first
    | (have i₁ := eq42453 X0 X1 x y
       have i₂ := eq93916
       grind)
    | exact superpose eq93916 eq42453
    | exact resolve eq42453 eq93916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42453
  have eq94131 : x = (M.op y y) := by
    first
    | (have i₁ := eq94115 x x
       have i₂ := eq310 x x x
       grind)
    | exact superpose eq310 eq94115
    | exact resolve eq94115 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310 eq94115
  have eq94520 : x ≠ x ∨ x = y ∨ x = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq94131
       grind)
    | exact superpose eq94131 eq13
    | exact resolve eq13 eq94131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94131
  have eq94650 : x = (k y y) ∨ x = y := by grind
  clear eq94520
  have eq273554 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ X0)))) ≠ (M.op (σ (k X0 X0)) (σ X0)) ∨ (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ X0)))) = (k (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ X0)))) (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ X0))))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq92307 (σ (k x x)) (σ x)
       have i₂ := eq33709 (σ x) x
       grind)
    | exact superpose eq33709 eq92307
    | (have j0 := eq92307 (σ X0) (σ X0)
       have j1 := eq33709 X0 X0
       grind)
    | exact resolve eq92307 eq33709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33709 eq92307
  have eq273981 : ∀ X0 : G, (σ X0) ≠ (M.op (σ (k X0 X0)) (σ X0)) ∨ (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ X0)))) = (k (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ X0)))) (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) (σ X0))))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq273554 X0
       have i₂ := eq66 (σ X0)
       grind)
    | exact superpose eq66 eq273554
    | (have j0 := eq273554 X0
       grind)
    | exact resolve eq273554 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273554
  have eq274427 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (σ X0) ≠ (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq273981 X0
       have i₂ := eq66 (σ X0)
       grind)
    | exact superpose eq66 eq273981
    | (have j0 := eq273981 X0
       grind)
    | exact resolve eq273981 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq273981
  have eq274584 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (σ X0) ≠ (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq274427 X0
       have j1 := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq274427 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | exact resolve eq274427 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274427
  have eq274661 : ∀ X0 : G, (σ X0) ≠ (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq274584 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq274584
    | (have j0 := eq274584 X0
       grind)
    | exact resolve eq274584 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274584
  have eq3192014 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq274661 y
       have i₂ := eq94650
       grind)
    | exact superpose eq94650 eq274661
    | exact resolve eq274661 eq94650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94650 eq274661
  have eq3193143 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3192014
       have i₂ := eq747 x y
       grind)
    | exact superpose eq747 eq3192014
    | (have j1 := eq747 x y
       grind)
    | exact resolve eq3192014 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747 eq3192014
  have eq3193144 : (σ y) ≠ (σ (k y x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3193143
       have r₂ := eq18364
       grind)
    | exact resolve eq3193143 eq18364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3193143
  have eq3193145 : (σ y) ≠ (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3193144
       have i₂ := eq18359
       grind)
    | exact superpose eq18359 eq3193144
    | exact resolve eq3193144 eq18359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18359 eq3193144
  have eq3193146 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq3193145
  have eq3193149 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq3193146
       grind)
    | exact superpose eq3193146 eq16
    | exact resolve eq16 eq3193146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3193146
  have eq3193694 : (σ x) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq3193149
       have i₂ := eq93916
       grind)
    | exact superpose eq93916 eq3193149
    | exact resolve eq3193149 eq93916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3193149
  have eq3193695 : x = y := by grind
  clear eq3193694
  have eq3193738 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3193695
       grind)
    | exact superpose eq3193695 eq16
    | exact resolve eq16 eq3193695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3193747 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq18364
       have i₂ := eq3193695
       grind)
    | exact superpose eq3193695 eq18364
    | exact resolve eq18364 eq3193695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18364
  have eq3193768 : x = (M.op x x) := by
    first
    | (have i₁ := eq93916
       have i₂ := eq3193695
       grind)
    | exact superpose eq3193695 eq93916
    | exact resolve eq93916 eq3193695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93916 eq3193695
  have eq3194109 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3193747
  have eq3369476 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3193738
       have i₂ := eq3193768
       grind)
    | exact superpose eq3193768 eq3193738
    | exact resolve eq3193738 eq3193768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3193738 eq3193768
  have eq3369477 : False := by grind
  exact eq3369477

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pxx_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : x ≠ (M.op x y) ∨ (M.op y y) = (k y x) := by
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
  have eq64 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
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
  have eq72 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq75 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (k y x) := by
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
  have eq76 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq111
    | exact resolve eq111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq113 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq112
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq112
    | exact resolve eq112 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq113
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq113
    | exact resolve eq113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq125 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
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
  clear eq37
  have eq618 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq622 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq52 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X4 X2 X3 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq53 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq52 X0 x x X3
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq812 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq842 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq843 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq842
    | exact resolve eq842 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq846 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq843
       have r₂ := eq27
       grind)
    | exact resolve eq843 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq848 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq846
    | exact resolve eq846 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq850 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq848
    | exact resolve eq848 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq852 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq850 eq27
    | exact resolve eq27 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq855 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq850 eq76
    | (have r₁ := eq76
       have r₂ := eq850
       grind)
    | exact resolve eq76 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq861 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq850
  have eq862 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq855
  have eq865 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq862
       have r₂ := eq861
       grind)
    | exact resolve eq862 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861 eq862
  have eq868 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq865 eq114
    | exact resolve eq114 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq869 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq865 eq82
    | exact resolve eq82 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq865
  have eq872 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq868
  have eq876 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq869
    | exact resolve eq869 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq869
  have eq877 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq872
       have r₂ := eq852
       grind)
    | exact resolve eq872 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852 eq872
  have eq880 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq876
       have r₂ := eq75
       grind)
    | exact resolve eq876 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq885 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq877 eq64
    | (have r₁ := eq64
       have r₂ := eq877
       grind)
    | exact resolve eq64 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq892 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq885
  have eq932 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq880
       grind)
    | exact superpose eq880 eq72
    | exact resolve eq72 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq937 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq932
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq932
    | exact resolve eq932 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932
  have eq943 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq937 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq944 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq943
  have eq948 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq944
    | exact resolve eq944 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq951 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq948
    | exact resolve eq948 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq952 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq951
  have eq955 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq952 eq27
    | exact resolve eq27 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq1152 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq892 eq114
    | exact resolve eq114 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq892
  have eq1155 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1152
  have eq1173 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op (M.op X1 X0) (σ (M.op x y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1155 eq14
    | exact resolve eq14 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155
  have eq1717 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1173 (M.op sF1 sF1) x
       have i₂ := eq682 sF1 x
       grind)
    | exact superpose eq682 eq1173
    | exact resolve eq1173 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173
  have eq1750 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1717
       have i₂ := eq53 sF1 sF1
       grind)
    | exact superpose eq53 eq1717
    | exact resolve eq1717 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717
  have eq1763 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1750 eq622
    | exact resolve eq622 eq1750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750
  have eq2671 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1763 eq622
    | exact resolve eq622 eq1763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622 eq1763
  have eq2687 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq51 eq2671
    | exact resolve eq2671 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2671
  have eq2742 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq877 eq2687
    | exact resolve eq2687 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877 eq2687
  have eq2757 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2742
  have eq2760 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2757
    | exact resolve eq2757 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2757
  have eq2761 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2760
       have r₂ := eq27
       grind)
    | exact resolve eq2760 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2760
  have eq2762 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2761 eq20
    | exact resolve eq20 eq2761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2767 : y ≠ y ∨ x = y ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2761 eq75
    | (have r₁ := eq75
       have r₂ := eq2761
       grind)
    | exact resolve eq75 eq2761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq2768 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2761 eq125
    | exact resolve eq125 eq2761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq2786 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq2761
  have eq2787 : x = y ∨ y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq2767
  have eq2797 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2768 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq2768
    | exact resolve eq2768 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq2768
  have eq2801 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2762
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2762
    | exact resolve eq2762 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2762
  have eq2922 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2801 eq955
    | (have r₁ := eq955
       have r₂ := eq2801
       grind)
    | exact resolve eq955 eq2801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq3006 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2922
  have eq3007 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3006
  have eq3034 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3007 eq64
    | (have r₁ := eq64
       have r₂ := eq3007
       grind)
    | exact resolve eq64 eq3007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq3061 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq3034
  have eq4839 : (M.op (σ y) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3061 eq2797
    | exact resolve eq2797 eq3061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2797
  have eq4841 : (M.op (σ y) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq4839
  have eq6014 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2787
       have r₂ := eq2786
       grind)
    | exact resolve eq2787 eq2786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2786 eq2787
  have eq6018 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq6014
       grind)
    | exact superpose eq6014 eq72
    | exact resolve eq72 eq6014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6014
  have eq6025 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6018
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6018
    | exact resolve eq6018 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6018
  have eq6027 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2801 eq6025
    | exact resolve eq6025 eq2801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2801
  have eq6040 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6025 eq3061
    | exact resolve eq3061 eq6025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3061 eq6025
  have eq6045 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq6040
  have eq6057 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq6027
  have eq6080 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6057 eq4841
    | exact resolve eq4841 eq6057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4841 eq6057
  have eq6086 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq6080
  have eq6102 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6045 eq51
    | exact resolve eq51 eq6045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq6045
  have eq7552 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3007 eq6102
    | exact resolve eq6102 eq3007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6102
  have eq7598 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq7552
  have eq7603 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq7598
    | exact resolve eq7598 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7598
  have eq7606 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3007 eq7603
    | exact resolve eq7603 eq3007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3007 eq7603
  have eq7650 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq7606
  have eq7707 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7650 eq53
    | exact resolve eq53 eq7650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq7650
  have eq7745 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq7707
    | exact resolve eq7707 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7707
  have eq8892 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7745 eq6086
    | exact resolve eq6086 eq7745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6086 eq7745
  have eq8950 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8892
  have eq8968 : x = (M.op x y) := by
    first
    | (have r₁ := eq8950
       have r₂ := eq27
       grind)
    | exact resolve eq8950 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8950
  have eq8971 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq8968 eq20
    | exact resolve eq20 eq8968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8973 : ∀ X0 : G, (M.op y (M.op x (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq8968 eq50
    | exact resolve eq50 eq8968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq8974 : x ≠ x ∨ (M.op y y) = (k y x) := by
    first
    | exact superpose eq8968 eq63
    | (have r₁ := eq63
       have r₂ := eq8968
       grind)
    | exact resolve eq63 eq8968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq8997 : (M.op y y) = (k y x) := by grind
  clear eq8974
  have eq9011 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq8971
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8971
    | exact resolve eq8971 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8971
  have eq9307 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq9011 eq26
    | exact resolve eq26 eq9011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq9364 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq9307 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq9307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9400 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq9364
       have r₂ := eq27
       grind)
    | exact resolve eq9364 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9364
  have eq9495 : (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq74 eq812
    | (have j0 := eq812 (M.op x y) y
       grind)
    | exact resolve eq812 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq812
  have eq9535 : (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq9495
    | exact resolve eq9495 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9495
  have eq9572 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq9535
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9535
    | exact resolve eq9535 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9535
  have eq9606 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq9572
    | exact resolve eq9572 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9572
  have eq9637 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq9307 eq9606
    | exact resolve eq9606 eq9307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9606
  have eq9666 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq9637
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9637
    | exact resolve eq9637 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq9637
  have eq9691 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq9666
    | exact resolve eq9666 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq9666
  have eq9708 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq9307 eq9691
    | exact resolve eq9691 eq9307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9307 eq9691
  have eq9720 : (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9708
       have r₂ := eq27
       grind)
    | exact resolve eq9708 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9708
  have eq9778 : (k (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq8997
       grind)
    | exact superpose eq8997 eq72
    | exact resolve eq72 eq8997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq8997
  have eq9785 : (k (σ y) (σ (M.op x y))) = (σ (M.op y y)) := by
    first
    | exact superpose eq9011 eq9778
    | exact resolve eq9778 eq9011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9778
  have eq11367 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq8973 (M.op X0 (M.op X0 X0))
       have i₂ := eq649 X0 X0 X0
       grind)
    | exact superpose eq649 eq8973
    | exact resolve eq8973 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq8973
  have eq15727 : ∀ X0 : G, (M.op X0 (M.op y (M.op x X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq618 X0
       have i₂ := eq11367 X0
       grind)
    | exact superpose eq11367 eq618
    | exact resolve eq618 eq11367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618 eq11367
  have eq15968 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op X0 X1) (M.op y y)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq672 y x X0 X1 y
       have i₂ := eq15727 y
       grind)
    | exact superpose eq15727 eq672
    | exact resolve eq672 eq15727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672 eq15727
  have eq16033 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq15968 x x
       have i₂ := eq682 y (M.op x x)
       grind)
    | exact superpose eq682 eq15968
    | exact resolve eq15968 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682 eq15968
  have eq16045 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16033
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16033
    | exact resolve eq16033 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq16033
  have eq16050 : x = (M.op y y) := by
    first
    | exact superpose eq8968 eq16045
    | exact resolve eq16045 eq8968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8968 eq16045
  have eq16053 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq9785
       have i₂ := eq16050
       grind)
    | exact superpose eq16050 eq9785
    | exact resolve eq9785 eq16050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9785 eq16050
  have eq16157 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq16053
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16053
    | exact resolve eq16053 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq16053
  have eq16172 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq9011 eq16157
    | exact resolve eq16157 eq9011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9011 eq16157
  have eq16183 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16172 eq9720
    | (have r₁ := eq9720
       have r₂ := eq16172
       grind)
    | exact resolve eq9720 eq16172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9720
  have eq16198 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16183
  have eq16309 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq16198 eq27
    | exact resolve eq27 eq16198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq16341 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq16198 eq9400
    | (have r₁ := eq9400
       have r₂ := eq16198
       grind)
    | exact resolve eq9400 eq16198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9400 eq16198
  have eq16342 : (σ y) = (k (σ y) (σ (M.op x y))) := by grind
  clear eq16341
  have eq16344 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq16172 eq16342
    | exact resolve eq16342 eq16172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16172 eq16342
  have eq16357 : False := by grind
  exact eq16357

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pyx_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq21 X0 X1
       have i₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact superpose eq14 eq21
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq21 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq80 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq63 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq63 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq63 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq105 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq107 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq105 X0 X1
       have j1 := eq80 X0 X1
       grind)
    | (have r₁ := eq105 X0 X1
       have r₂ := eq80 X0 X1
       grind)
    | (have r₁ := eq105 X0 X0
       have r₂ := eq80 X0 X0
       grind)
    | exact resolve eq105 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq105
  have eq467 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq107 (σ X1) (σ X0)
       grind)
    | exact superpose eq107 eq15
    | exact resolve eq15 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq467 X0 X1
       have i₂ := eq107 X1 X0
       grind)
    | exact superpose eq107 eq467
    | exact resolve eq467 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq467
  have eq474 : False := by grind
  exact eq474
