import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxy_y_pxx_x_pxy_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X3 X1
       have i₂ := eq14 X0 X1 X2
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
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x x) = (M.op y x) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x x) = (M.op y x) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x x) = (M.op y x) := by
    first
    | exact superpose eq20 eq94
    | exact resolve eq94 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq97 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96
    | exact resolve eq96 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq236 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
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
  have eq240 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
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
  have eq289 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq278 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq278
    | exact resolve eq278 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq291 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq289 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq289
    | exact resolve eq289 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq289
  have eq637 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) X2)) y) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq638 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) X2)) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq658 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
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
  clear eq52
  have eq683 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq291 X0
       grind)
    | exact superpose eq291 eq16
    | exact resolve eq16 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq1112 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x x) y) := by
    intro X0
    first
    | (have i₁ := eq658 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq658
    | (have j0 := eq658 x y X0
       grind)
    | exact resolve eq658 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1113 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq658
    | (have j0 := eq658 (σ x) (σ y) X0
       grind)
    | exact resolve eq658 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1127 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq658 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq658
    | (have j0 := eq658 x X0 y
       grind)
    | exact resolve eq658 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1128 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq658
    | (have j0 := eq658 (σ x) X0 (σ y)
       grind)
    | exact resolve eq658 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1132 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq658 X0 X1 x
       grind)
    | exact superpose eq658 eq14
    | exact resolve eq14 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1203 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1132 X0 (M.op X0 X1)
       have i₂ := eq658 X0 X0 X1
       grind)
    | exact superpose eq658 eq1132
    | exact resolve eq1132 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1204 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1132 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq1132 X0 (M.op X0 X0)
       grind)
    | exact superpose eq1132 eq1132
    | exact resolve eq1132 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1208 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1 X1 X0
       have i₂ := eq1132 (M.op X0 X1) X0
       grind)
    | exact superpose eq1132 eq55
    | exact resolve eq55 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1213 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X1
       have i₂ := eq1132 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq1132 eq14
    | exact resolve eq14 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1229 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1208 X0 X1
       have i₂ := eq658 X0 X1 X1
       grind)
    | exact superpose eq658 eq1208
    | exact resolve eq1208 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq1235 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1204 (σ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq1204
    | exact resolve eq1204 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1237 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1204 (τ X0)
       have i₂ := eq683 X0
       grind)
    | exact superpose eq683 eq1204
    | exact resolve eq1204 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683 eq1204
  have eq1315 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq1127 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1127
    | (have j0 := eq1127 y
       grind)
    | exact resolve eq1127 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127
  have eq1353 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1315
       have i₂ := eq1112 X0
       grind)
    | exact superpose eq1112 eq1315
    | exact resolve eq1315 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1504 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq26 eq1128
    | (have j0 := eq1128 (σ y)
       grind)
    | exact resolve eq1128 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128
  have eq1542 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1113 eq1504
    | exact resolve eq1504 eq1113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1809 : (M.op x x) = (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op x x)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1203 (M.op x x) y
       have i₂ := eq1315
       grind)
    | exact superpose eq1315 eq1203
    | exact resolve eq1203 eq1315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315
  have eq1813 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) x) := by
    first
    | exact superpose eq236 eq1203
    | exact resolve eq1203 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1815 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1504 eq1203
    | exact resolve eq1203 eq1504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504
  have eq1819 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq245 eq1203
    | exact resolve eq1203 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1849 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq1819
       have i₂ := eq1132 sF4 (M.op sF4 sF4)
       grind)
    | exact superpose eq1132 eq1819
    | exact resolve eq1819 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1819
  have eq1853 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1815
       have i₂ := eq1132 sF2 (M.op sF2 sF2)
       grind)
    | exact superpose eq1132 eq1815
    | exact resolve eq1815 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815
  have eq1855 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1813
       have i₂ := eq1132 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq1132 eq1813
    | exact resolve eq1813 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1813
  have eq1859 : (M.op x x) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1809
       have i₂ := eq1132 x (M.op x x)
       grind)
    | exact superpose eq1132 eq1809
    | exact resolve eq1809 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132 eq1809
  have eq1897 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1849 eq245
    | exact resolve eq245 eq1849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq1905 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1849 eq658
    | exact resolve eq658 eq1849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1918 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq1905 x
       have i₂ := eq658 sF4 sF2 x
       grind)
    | exact superpose eq658 eq1905
    | exact resolve eq1905 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1905
  have eq1922 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq1849 eq1918
    | exact resolve eq1918 eq1849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1918
  have eq1980 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq1855 eq236
    | exact resolve eq236 eq1855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq1989 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1855 eq658
    | exact resolve eq658 eq1855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2003 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | (have i₁ := eq1989 x
       have i₂ := eq658 sF0 x x
       grind)
    | exact superpose eq658 eq1989
    | exact resolve eq1989 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1989
  have eq2007 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq1855 eq2003
    | exact resolve eq2003 eq1855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2003
  have eq2179 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq1849 eq1853
    | exact resolve eq1853 eq1849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853
  have eq2180 : (M.op x x) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq1855 eq1859
    | exact resolve eq1859 eq1855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1859
  have eq2909 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1229 (M.op X0 X1) X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq1229
    | exact resolve eq1229 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2917 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1229 (M.op (M.op X0 X0) X0) (M.op X0 X1)
       have i₂ := eq1203 X0 X1
       grind)
    | exact superpose eq1203 eq1229
    | exact resolve eq1229 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203
  have eq2995 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2917 X0 X1
       have i₂ := eq1213 X0 X0
       grind)
    | exact superpose eq1213 eq2917
    | exact resolve eq2917 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213 eq2917
  have eq3001 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2995 X0 X1
       have i₂ := eq658 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq658 eq2995
    | exact resolve eq2995 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2995
  have eq3002 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3001 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq3001
    | exact resolve eq3001 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3001
  have eq3951 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2909 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq2909 X0 X1
       grind)
    | exact superpose eq2909 eq2909
    | exact resolve eq2909 eq2909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4013 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3002 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq2909 X0 X1
       grind)
    | exact superpose eq2909 eq3002
    | exact resolve eq3002 eq2909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3002
  have eq4014 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4013 X0 X1
       have i₂ := eq658 (M.op X0 X1) X1 X1
       grind)
    | exact superpose eq658 eq4013
    | exact resolve eq4013 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4013
  have eq4053 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3951 X0 X1
       have i₂ := eq1229 X0 (M.op X0 X1)
       grind)
    | exact superpose eq1229 eq3951
    | exact resolve eq3951 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3951
  have eq4066 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4014 X0 X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq4014
    | exact resolve eq4014 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4014
  have eq4088 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4053 X0 X1
       have i₂ := eq658 X0 X0 X1
       grind)
    | exact superpose eq658 eq4053
    | exact resolve eq4053 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4053
  have eq4600 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) y) := by
    intro X1
    first
    | exact superpose eq1353 eq240
    | (have j0 := eq240 y X1
       grind)
    | exact resolve eq240 eq1353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq4601 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) y) := by
    intro X1
    first
    | exact superpose eq1855 eq4600
    | exact resolve eq4600 eq1855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4600
  have eq4618 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq4601 eq2909
    | exact resolve eq2909 eq4601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4601
  have eq4624 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op x (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq1980 eq4618
    | exact resolve eq4618 eq1980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1980 eq4618
  have eq4632 : ∀ X0 : G, (M.op x x) = (M.op x (M.op (M.op (M.op x y) x) X0)) := by
    intro X0
    first
    | exact superpose eq2180 eq4624
    | exact resolve eq4624 eq2180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2180 eq4624
  have eq5018 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1542 eq249
    | (have j0 := eq249 (σ y) X1
       grind)
    | exact resolve eq249 eq1542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq5019 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1849 eq5018
    | exact resolve eq5018 eq1849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5018
  have eq5336 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq5019 eq2909
    | exact resolve eq2909 eq5019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5019
  have eq5344 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq1897 eq5336
    | exact resolve eq5336 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897 eq5336
  have eq5352 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq2179 eq5344
    | exact resolve eq5344 eq2179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2179 eq5344
  have eq6314 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4088 X0 X2
       have i₂ := eq4088 X0 X1
       grind)
    | (have i₁ := eq4088 X1 X1
       have i₂ := eq4088 X1 X1
       grind)
    | exact superpose eq4088 eq4088
    | exact resolve eq4088 eq4088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4088
  have eq12419 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1353 eq637
    | (have j0 := eq637 y X1 X2
       grind)
    | exact resolve eq637 eq1353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637 eq1353
  have eq12420 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) x) X1)) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1855 eq12419
    | exact resolve eq12419 eq1855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1855 eq12419
  have eq12421 : ∀ X2 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x x) X2)) y) := by
    intro X2
    first
    | exact superpose eq4632 eq12420
    | exact resolve eq12420 eq4632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4632 eq12420
  have eq12506 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x y) (M.op x X0))) y) := by
    intro X0
    first
    | (have i₁ := eq12421 y
       have i₂ := eq1112 X0
       grind)
    | exact superpose eq1112 eq12421
    | exact resolve eq12421 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112 eq12421
  have eq12557 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) y) := by
    first
    | (have i₁ := eq12506 x
       have i₂ := eq658 sF0 x (M.op x x)
       grind)
    | exact superpose eq658 eq12506
    | exact resolve eq12506 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12506
  have eq12579 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) y) := by
    first
    | (have i₁ := eq12557
       have i₂ := eq1229 sF0 x
       grind)
    | exact superpose eq1229 eq12557
    | exact resolve eq12557 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12557
  have eq12595 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) x) y) := by
    first
    | exact superpose eq2007 eq12579
    | exact resolve eq12579 eq2007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2007 eq12579
  have eq12611 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) X0) X0) y) := by
    intro X0
    first
    | (have i₁ := eq12595
       have i₂ := eq6314 sF0 x x
       grind)
    | (have i₁ := eq12595
       have i₂ := eq6314 sF0 x x
       grind)
    | exact superpose eq6314 eq12595
    | exact resolve eq12595 eq6314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12595
  have eq12734 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1542 eq638
    | (have j0 := eq638 (σ y) X1 X2
       grind)
    | exact resolve eq638 eq1542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638 eq1542
  have eq12735 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1849 eq12734
    | exact resolve eq12734 eq1849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1849 eq12734
  have eq12736 : ∀ X2 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ x)) X2)) (σ y)) := by
    intro X2
    first
    | exact superpose eq5352 eq12735
    | exact resolve eq12735 eq5352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5352 eq12735
  have eq12742 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) (σ y)) := by
    intro X0
    first
    | exact superpose eq1113 eq12736
    | exact resolve eq12736 eq1113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113 eq12736
  have eq12793 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq12742 x
       have i₂ := eq658 sF4 sF2 (M.op sF2 x)
       grind)
    | exact superpose eq658 eq12742
    | exact resolve eq12742 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq12742
  have eq12815 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq12793
       have i₂ := eq1229 sF4 sF2
       grind)
    | exact superpose eq1229 eq12793
    | exact resolve eq12793 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229 eq12793
  have eq12831 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1922 eq12815
    | exact resolve eq12815 eq1922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1922 eq12815
  have eq12847 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12831
       have i₂ := eq6314 sF4 sF2 x
       grind)
    | (have i₁ := eq12831
       have i₂ := eq6314 sF4 x sF2
       grind)
    | exact superpose eq6314 eq12831
    | exact resolve eq12831 eq6314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6314 eq12831
  have eq58091 : y = (M.op (M.op (M.op x x) x) (M.op x x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2909 y x
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq2909
    | exact resolve eq2909 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq58115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq58091
       have i₂ := eq2909 x x
       grind)
    | exact superpose eq2909 eq58091
    | exact resolve eq58091 eq2909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58091
  have eq58135 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq58115 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq58115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58115
  have eq58145 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq58135
    | exact resolve eq58135 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58135
  have eq58156 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq58145
       have r₂ := eq27
       grind)
    | exact resolve eq58145 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58145
  have eq58160 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq58156
    | exact resolve eq58156 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58156
  have eq58176 : (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (σ x) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq58160 eq2909
    | exact resolve eq2909 eq58160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58160
  have eq58200 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq58176
       have i₂ := eq2909 sF2 sF2
       grind)
    | exact superpose eq2909 eq58176
    | exact resolve eq58176 eq2909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2909 eq58176
  have eq58265 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ y) X0) X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq58200 eq12847
    | exact resolve eq12847 eq58200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12847 eq58200
  have eq58301 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq58265 x
       have i₂ := eq4066 sF3 x
       grind)
    | exact superpose eq4066 eq58265
    | exact resolve eq58265 eq4066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58265
  have eq58719 : (τ (σ y)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq58301 eq1237
    | exact resolve eq1237 eq58301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237 eq58301
  have eq58785 : y = (M.op (τ (σ x)) y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq58719
    | exact resolve eq58719 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58719
  have eq58811 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq58785
    | exact resolve eq58785 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58785
  have eq58817 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq58811
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq58811
    | exact resolve eq58811 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58811
  have eq58818 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq58817
  have eq58820 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq58818 eq29
    | exact resolve eq29 eq58818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq58818
  have eq59004 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq58820
    | exact resolve eq58820 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq58820
  have eq59005 : y = (M.op x y) ∨ x = y := by grind
  clear eq59004
  have eq59381 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq59005 eq20
    | exact resolve eq20 eq59005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59490 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op y X0) X0) y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq59005 eq12611
    | exact resolve eq12611 eq59005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12611 eq59005
  have eq59532 : y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq59490 x
       have i₂ := eq4066 y x
       grind)
    | exact superpose eq4066 eq59490
    | exact resolve eq59490 eq4066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4066 eq59490
  have eq59595 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq59381
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq59381
    | exact resolve eq59381 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59381
  have eq59898 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1235 x
       have i₂ := eq59532
       grind)
    | exact superpose eq59532 eq1235
    | exact resolve eq1235 eq59532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235 eq59532
  have eq59965 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq59898
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq59898
    | exact resolve eq59898 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59898
  have eq59994 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq59965
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq59965
    | exact resolve eq59965 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59965
  have eq60003 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq59994
    | exact resolve eq59994 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59994
  have eq60355 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq60003 eq27
    | exact resolve eq27 eq60003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60003
  have eq60457 : x = y := by
    first
    | (have r₁ := eq60355
       have r₂ := eq59595
       grind)
    | exact resolve eq60355 eq59595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59595 eq60355
  have eq60459 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq60457
       grind)
    | exact superpose eq60457 eq18
    | exact resolve eq18 eq60457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq60460 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq60457
       grind)
    | exact superpose eq60457 eq24
    | exact resolve eq24 eq60457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq60457
  have eq60648 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq60460
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq60460
    | exact resolve eq60460 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq60460
  have eq60679 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq60648 eq26
    | exact resolve eq26 eq60648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq60648
  have eq61145 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq60679 eq71
    | exact resolve eq71 eq60679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq60679
  have eq61331 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq61145
       have i₂ := eq60459
       grind)
    | exact superpose eq60459 eq61145
    | exact resolve eq61145 eq60459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60459 eq61145
  have eq61365 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq61331 eq15
    | exact resolve eq15 eq61331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61331
  have eq61456 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq61365
    | exact resolve eq61365 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq61365
  have eq61482 : False := by grind
  exact eq61482

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_pyy_pxx_y_pyx_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X3 X1
       have i₂ := eq14 X0 X1 X2
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
  have eq69 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq43
    | exact resolve eq43 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
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
  have eq72 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq69
    | exact resolve eq69 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
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
  have eq77 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = (k y x) := by
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
  have eq78 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq98 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq99 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq103 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq99
       have i₂ := eq66 sF3
       grind)
    | exact superpose eq66 eq99
    | exact resolve eq99 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq105 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq103
       have i₂ := eq66 y
       grind)
    | exact superpose eq66 eq103
    | exact resolve eq103 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq98
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq98 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq16
    | exact resolve eq16 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107
    | exact resolve eq107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
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
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq236 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
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
  clear eq50
  have eq243 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq654 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
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
  clear eq52
  have eq855 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq73 X1
       grind)
    | exact superpose eq73 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq856 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq855 X0 X1
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq855
    | (have j0 := eq855 X0 X1
       grind)
    | exact resolve eq855 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq895 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ X0) (σ y)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq856 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq856
    | (have j0 := eq856 y X0
       grind)
    | exact resolve eq856 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq918 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq895 X0
       have i₂ := eq105
       grind)
    | exact superpose eq105 eq895
    | (have j0 := eq895 X0
       grind)
    | exact resolve eq895 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq895
  have eq1070 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq654
    | (have j0 := eq654 (σ x) (σ y) X0
       grind)
    | exact resolve eq654 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1084 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq654 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq654
    | (have j0 := eq654 x X0 y
       grind)
    | exact resolve eq654 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1085 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq654
    | (have j0 := eq654 (σ x) X0 (σ y)
       grind)
    | exact resolve eq654 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1089 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq654 X0 X1 x
       grind)
    | exact superpose eq654 eq14
    | exact resolve eq14 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1158 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1089 (σ X0) X1
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq1089
    | exact resolve eq1089 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1161 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1089 X0 (M.op X0 X1)
       have i₂ := eq654 X0 X0 X1
       grind)
    | exact superpose eq654 eq1089
    | exact resolve eq1089 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1166 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1 X1 X0
       have i₂ := eq1089 (M.op X0 X1) X0
       grind)
    | exact superpose eq1089 eq55
    | exact resolve eq55 eq1089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1171 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X1
       have i₂ := eq1089 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq1089 eq14
    | exact resolve eq14 eq1089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1186 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1166 X0 X1
       have i₂ := eq654 X0 X1 X1
       grind)
    | exact superpose eq654 eq1166
    | exact resolve eq1166 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166
  have eq1271 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq1084 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1084
    | (have j0 := eq1084 y
       grind)
    | exact resolve eq1084 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1455 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq26 eq1085
    | (have j0 := eq1085 (σ y)
       grind)
    | exact resolve eq1085 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq1491 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1070 eq1455
    | exact resolve eq1455 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070
  have eq1753 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) x) := by
    first
    | exact superpose eq236 eq1161
    | exact resolve eq1161 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1755 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1455 eq1161
    | exact resolve eq1161 eq1455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1759 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq243 eq1161
    | exact resolve eq1161 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1790 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq1759
       have i₂ := eq1089 sF4 (M.op sF4 sF4)
       grind)
    | exact superpose eq1089 eq1759
    | exact resolve eq1759 eq1089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1759
  have eq1794 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1755
       have i₂ := eq1089 sF2 (M.op sF2 sF2)
       grind)
    | exact superpose eq1089 eq1755
    | exact resolve eq1755 eq1089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755
  have eq1796 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1753
       have i₂ := eq1089 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq1089 eq1753
    | exact resolve eq1753 eq1089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753
  have eq1839 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1790 eq243
    | exact resolve eq243 eq1790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1923 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq1796 eq236
    | exact resolve eq236 eq1796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2121 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq1790 eq1794
    | exact resolve eq1794 eq1790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1794
  have eq2850 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1186 (M.op X0 X1) X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq1186
    | exact resolve eq1186 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2852 : x = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | exact superpose eq236 eq1186
    | exact resolve eq1186 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2854 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq243 eq1186
    | exact resolve eq1186 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq2858 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1186 (M.op (M.op X0 X0) X0) (M.op X0 X1)
       have i₂ := eq1161 X0 X1
       grind)
    | exact superpose eq1161 eq1186
    | exact resolve eq1186 eq1161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161
  have eq2935 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2858 X0 X1
       have i₂ := eq1171 X0 X0
       grind)
    | exact superpose eq1171 eq2858
    | exact resolve eq2858 eq1171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171 eq2858
  have eq2941 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2935 X0 X1
       have i₂ := eq654 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq654 eq2935
    | exact resolve eq2935 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2935
  have eq2942 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2941 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq2941
    | exact resolve eq2941 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2941
  have eq3388 : (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = (M.op (M.op (M.op x y) y) x) := by
    first
    | exact superpose eq2852 eq2942
    | exact resolve eq2942 eq2852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3403 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq2942 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2942
    | (have j0 := eq2942 x y
       grind)
    | exact resolve eq2942 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3409 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq2942
    | (have j0 := eq2942 (σ x) (σ y)
       grind)
    | exact resolve eq2942 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2942
  have eq3478 : (M.op (M.op (M.op x y) (M.op x y)) y) = (M.op (M.op (M.op x y) y) x) := by
    first
    | (have i₁ := eq3388
       have i₂ := eq654 sF0 y y
       grind)
    | exact superpose eq654 eq3388
    | exact resolve eq3388 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3388
  have eq3514 : x = (M.op (M.op (M.op x y) y) x) := by
    first
    | exact superpose eq236 eq3478
    | exact resolve eq3478 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq3478
  have eq3545 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq3403 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 (M.op x y) x
       have r₂ := eq3403
       grind)
    | exact resolve eq12 eq3403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3403
  have eq3558 : (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) := by grind
  clear eq3545
  have eq3562 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq1796 eq3558
    | exact resolve eq3558 eq1796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3558
  have eq3567 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq3409 eq12
    | (have j0 := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq3409
       grind)
    | exact resolve eq12 eq3409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3409
  have eq3580 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq3567
  have eq3584 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1790 eq3580
    | exact resolve eq3580 eq1790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3580
  have eq3871 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2850 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq2850 X0 X1
       grind)
    | exact superpose eq2850 eq2850
    | exact resolve eq2850 eq2850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3971 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3871 X0 X1
       have i₂ := eq1186 X0 (M.op X0 X1)
       grind)
    | exact superpose eq1186 eq3871
    | exact resolve eq3871 eq1186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186 eq3871
  have eq4005 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3971 X0 X1
       have i₂ := eq654 X0 X0 X1
       grind)
    | exact superpose eq654 eq3971
    | exact resolve eq3971 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq3971
  have eq4923 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1491 eq246
    | (have j0 := eq246 (σ y) X1
       grind)
    | exact resolve eq246 eq1491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq1491
  have eq4924 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1790 eq4923
    | exact resolve eq4923 eq1790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4923
  have eq5243 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq4924 eq2850
    | exact resolve eq2850 eq4924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4924
  have eq5251 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq1839 eq5243
    | exact resolve eq5243 eq1839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5243
  have eq5258 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq2121 eq5251
    | exact resolve eq5251 eq2121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2121 eq5251
  have eq6185 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4005 X0 X2
       have i₂ := eq4005 X0 X1
       grind)
    | (have i₁ := eq4005 X1 X1
       have i₂ := eq4005 X1 X1
       grind)
    | exact superpose eq4005 eq4005
    | exact resolve eq4005 eq4005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4005
  have eq7690 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq918 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq918
    | (have j0 := eq918 x
       grind)
    | exact resolve eq918 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq7720 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq7690
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq7690
    | exact resolve eq7690 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7690
  have eq7738 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | exact superpose eq26 eq7720
    | exact resolve eq7720 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7720
  have eq7749 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | exact superpose eq26 eq7738
    | exact resolve eq7738 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7738
  have eq7758 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq7749
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq7749
    | exact resolve eq7749 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7749
  have eq7766 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq7758
    | exact resolve eq7758 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7758
  have eq9325 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) y) X0) X0) := by
    intro X0
    first
    | exact superpose eq3514 eq6185
    | exact resolve eq6185 eq3514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3514 eq6185
  have eq43070 : x = (M.op (M.op x x) y) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq3562 eq1923
    | exact resolve eq1923 eq3562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1923 eq3562
  have eq43178 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq43070
       have i₂ := eq1271
       grind)
    | exact superpose eq1271 eq43070
    | exact resolve eq43070 eq1271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271 eq43070
  have eq43190 : x = (k (M.op x y) x) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1796 eq43178
    | exact resolve eq43178 eq1796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796 eq43178
  have eq45692 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq3584 eq1839
    | exact resolve eq1839 eq3584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1839 eq3584
  have eq45790 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1455 eq45692
    | exact resolve eq45692 eq1455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1455 eq45692
  have eq45803 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1790 eq45790
    | exact resolve eq45790 eq1790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1790 eq45790
  have eq54264 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq116 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq54273 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq54264
    | exact resolve eq54264 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54264
  have eq54284 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq54273
       have r₂ := eq27
       grind)
    | exact resolve eq54273 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54273
  have eq54288 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq54284
    | exact resolve eq54284 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54284
  have eq54292 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq54288
    | exact resolve eq54288 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54288
  have eq54312 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq54292 eq1089
    | exact resolve eq1089 eq54292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54292
  have eq58664 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq54312 eq5258
    | exact resolve eq5258 eq54312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5258 eq54312
  have eq58793 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq58664
    | exact resolve eq58664 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58664
  have eq58794 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq58793
  have eq58836 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq58794 eq78
    | (have r₁ := eq78
       have r₂ := eq58794
       grind)
    | exact resolve eq78 eq58794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq58794
  have eq58943 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq58836
  have eq78511 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq58943 eq2850
    | exact resolve eq2850 eq58943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58943
  have eq78524 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq2854 eq78511
    | exact resolve eq78511 eq2854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78511
  have eq78542 : (τ (σ x)) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq78524 eq112
    | exact resolve eq112 eq78524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq78524
  have eq78574 : x = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq28 eq78542
    | exact resolve eq78542 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78542
  have eq78584 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have r₁ := eq78574
       have r₂ := eq77
       grind)
    | exact resolve eq78574 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq78574
  have eq78939 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) X0) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq1089 y X0
       have i₂ := eq78584
       grind)
    | exact superpose eq78584 eq1089
    | exact resolve eq1089 eq78584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089 eq78584
  have eq80375 : (M.op y y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq78939 eq9325
    | exact resolve eq9325 eq78939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9325 eq78939
  have eq86502 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x x)) X0) X0) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq1158 y X0
       have i₂ := eq80375
       grind)
    | exact superpose eq80375 eq1158
    | exact resolve eq1158 eq80375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80375
  have eq86575 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq86502 x
       have i₂ := eq1158 x x
       grind)
    | exact superpose eq1158 eq86502
    | exact resolve eq86502 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158 eq86502
  have eq86609 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq86575
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq86575
    | exact resolve eq86575 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86575
  have eq86617 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq86609
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq86609
    | exact resolve eq86609 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86609
  have eq86618 : x = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq86617
  have eq86955 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq86618
       grind)
    | exact superpose eq86618 eq98
    | exact resolve eq98 eq86618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq86965 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq86618
       grind)
    | exact superpose eq86618 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq86618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86618
  have eq86981 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq86965
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq86965
    | exact resolve eq86965 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86965
  have eq86991 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq86955
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq86955
    | exact resolve eq86955 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86955
  have eq86998 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq86981
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq86981
    | exact resolve eq86981 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86981
  have eq87007 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq86998
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq86998
    | exact resolve eq86998 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86998
  have eq87055 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq7766 eq86991
    | exact resolve eq86991 eq7766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7766 eq86991
  have eq153720 : y = (M.op (M.op (M.op x y) y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2850 y y
       have i₂ := eq87007
       grind)
    | exact superpose eq87007 eq2850
    | exact resolve eq2850 eq87007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87007
  have eq153736 : (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2852 eq153720
    | exact resolve eq153720 eq2852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2852 eq153720
  have eq154453 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq153736
       grind)
    | exact superpose eq153736 eq72
    | exact resolve eq72 eq153736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153736
  have eq154649 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq154453
    | exact resolve eq154453 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154453
  have eq166327 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq87055 eq2850
    | exact resolve eq2850 eq87055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2850 eq87055
  have eq166346 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2854 eq166327
    | exact resolve eq166327 eq2854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2854 eq166327
  have eq166347 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq166346
  have eq166406 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq166347 eq154649
    | exact resolve eq154649 eq166347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166504 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq166406
  have eq166556 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq166504
       have r₂ := eq27
       grind)
    | exact resolve eq166504 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166504
  have eq167516 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq166556 eq27
    | exact resolve eq27 eq166556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167585 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq166556 eq45803
    | exact resolve eq45803 eq166556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45803 eq166556
  have eq167731 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq167585
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq167585
    | exact resolve eq167585 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167585
  have eq167732 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq167731
  have eq173197 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq167732 eq154649
    | exact resolve eq154649 eq167732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154649 eq167732
  have eq173304 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq173197
  have eq173365 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq173304
       have r₂ := eq167516
       grind)
    | exact resolve eq173304 eq167516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167516 eq173304
  have eq173433 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq173365 eq29
    | exact resolve eq29 eq173365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173365
  have eq173654 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq173433
    | exact resolve eq173433 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173433
  have eq173655 : x = (M.op x y) ∨ x = y := by grind
  clear eq173654
  have eq173685 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq173655 eq20
    | exact resolve eq20 eq173655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173886 : x = (k x x) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq173655 eq43190
    | exact resolve eq43190 eq173655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43190 eq173655
  have eq173967 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq173886
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq173886
    | exact resolve eq173886 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq173886
  have eq173968 : x = (M.op x x) ∨ x = y := by grind
  clear eq173967
  have eq174136 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq173685
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq173685
    | exact resolve eq173685 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173685
  have eq175259 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq72
       have i₂ := eq173968
       grind)
    | exact superpose eq173968 eq72
    | exact resolve eq72 eq173968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq173968
  have eq175482 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq175259
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq175259
    | exact resolve eq175259 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175259
  have eq177946 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq175482 eq166347
    | exact resolve eq166347 eq175482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166347 eq175482
  have eq178051 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq177946
  have eq188866 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq178051 eq27
    | exact resolve eq27 eq178051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178051
  have eq189179 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq188866
       have r₂ := eq174136
       grind)
    | exact resolve eq188866 eq174136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174136 eq188866
  have eq189248 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq189179 eq29
    | exact resolve eq29 eq189179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq189179
  have eq189470 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq189248
    | exact resolve eq189248 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq189248
  have eq189471 : x = y := by grind
  clear eq189470
  have eq189501 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq189471
       grind)
    | exact superpose eq189471 eq18
    | exact resolve eq18 eq189471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq189502 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq189471
       grind)
    | exact superpose eq189471 eq24
    | exact resolve eq24 eq189471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq189471
  have eq189955 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq189502
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq189502
    | exact resolve eq189502 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq189502
  have eq190020 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq189955 eq26
    | exact resolve eq26 eq189955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq189955
  have eq190579 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq190020 eq71
    | exact resolve eq71 eq190020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq190020
  have eq190793 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq190579
       have i₂ := eq189501
       grind)
    | exact superpose eq189501 eq190579
    | exact resolve eq190579 eq189501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189501 eq190579
  have eq190876 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq190793 eq15
    | exact resolve eq15 eq190793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190793
  have eq191220 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq190876
    | exact resolve eq190876 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq190876
  have eq191327 : False := by grind
  exact eq191327

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,X) else if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxx_pxy_pxx_x_pxy_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X3 X1
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
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq10
    | exact resolve eq10 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq43
    | exact resolve eq43 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq71 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq49
    | exact resolve eq49 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq71
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq71
    | exact resolve eq71 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq73 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq70
    | exact resolve eq70 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq69
    | exact resolve eq69 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq78 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) := by
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
  have eq79 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq95
    | exact resolve eq95 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq99 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
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
  have eq239 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
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
  have eq243 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq571 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) X2)) y) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq572 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) X2)) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq580 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) X3) := by
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
  have eq592 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
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
  have eq701 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) X5)) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3 X2 X3
       have i₂ := eq55 X0 X1 X2 X3
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq893 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq912 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq893 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq893
    | (have j0 := eq893 X0 y
       grind)
    | exact resolve eq893 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq1194 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x x) y) := by
    intro X0
    first
    | (have i₁ := eq592 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq592
    | (have j0 := eq592 x y X0
       grind)
    | exact resolve eq592 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1195 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq592
    | (have j0 := eq592 (σ x) (σ y) X0
       grind)
    | exact resolve eq592 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1210 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq592 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq592
    | (have j0 := eq592 x X0 y
       grind)
    | exact resolve eq592 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1211 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq592
    | (have j0 := eq592 (σ x) X0 (σ y)
       grind)
    | exact resolve eq592 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1217 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq592 X0 X1 x
       grind)
    | exact superpose eq592 eq14
    | exact resolve eq14 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1301 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1217 (σ X0) X1
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq1217
    | exact resolve eq1217 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1303 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1217 X0 (M.op X0 X1)
       have i₂ := eq592 X0 X0 X1
       grind)
    | exact superpose eq592 eq1217
    | exact resolve eq1217 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1308 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1 X1 X0
       have i₂ := eq1217 (M.op X0 X1) X0
       grind)
    | exact superpose eq1217 eq55
    | exact resolve eq55 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1315 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X1
       have i₂ := eq1217 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq1217 eq14
    | exact resolve eq14 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1338 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1308 X0 X1
       have i₂ := eq592 X0 X1 X1
       grind)
    | exact superpose eq592 eq1308
    | exact resolve eq1308 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308
  have eq1476 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq1210 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1210
    | (have j0 := eq1210 y
       grind)
    | exact resolve eq1210 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq1536 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1476
       have i₂ := eq1194 X0
       grind)
    | exact superpose eq1194 eq1476
    | exact resolve eq1476 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1721 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq26 eq1211
    | (have j0 := eq1211 (σ y)
       grind)
    | exact resolve eq1211 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq1781 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1195 eq1721
    | exact resolve eq1721 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2114 : (M.op x x) = (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op x x)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1303 (M.op x x) y
       have i₂ := eq1476
       grind)
    | exact superpose eq1476 eq1303
    | exact resolve eq1303 eq1476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2118 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) x) := by
    first
    | exact superpose eq239 eq1303
    | exact resolve eq1303 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2120 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1721 eq1303
    | exact resolve eq1303 eq1721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2124 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq248 eq1303
    | exact resolve eq1303 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2165 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq2124
       have i₂ := eq1217 sF4 (M.op sF4 sF4)
       grind)
    | exact superpose eq1217 eq2124
    | exact resolve eq2124 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2124
  have eq2169 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq2120
       have i₂ := eq1217 sF2 (M.op sF2 sF2)
       grind)
    | exact superpose eq1217 eq2120
    | exact resolve eq2120 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2120
  have eq2171 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq2118
       have i₂ := eq1217 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq1217 eq2118
    | exact resolve eq2118 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2118
  have eq2175 : (M.op x x) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq2114
       have i₂ := eq1217 x (M.op x x)
       grind)
    | exact superpose eq1217 eq2114
    | exact resolve eq2114 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217 eq2114
  have eq2218 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq2165 eq248
    | exact resolve eq248 eq2165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq2231 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2165 eq592
    | exact resolve eq592 eq2165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2243 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq2231 x
       have i₂ := eq592 sF4 sF2 x
       grind)
    | exact superpose eq592 eq2231
    | exact resolve eq2231 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2231
  have eq2250 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq2165 eq2243
    | exact resolve eq2243 eq2165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2243
  have eq2317 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq2171 eq239
    | exact resolve eq239 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq2331 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2171 eq592
    | exact resolve eq592 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2344 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | (have i₁ := eq2331 x
       have i₂ := eq592 sF0 x x
       grind)
    | exact superpose eq592 eq2331
    | exact resolve eq2331 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2331
  have eq2351 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq2171 eq2344
    | exact resolve eq2344 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2344
  have eq2550 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq2165 eq2169
    | exact resolve eq2169 eq2165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2169
  have eq2551 : (M.op x x) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq2171 eq2175
    | exact resolve eq2175 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2175
  have eq3282 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1338 (M.op X0 X1) X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq1338
    | exact resolve eq1338 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3290 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1338 (M.op (M.op X0 X0) X0) (M.op X0 X1)
       have i₂ := eq1303 X0 X1
       grind)
    | exact superpose eq1303 eq1338
    | exact resolve eq1338 eq1303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3384 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3290 X0 X1
       have i₂ := eq1315 X0 X0
       grind)
    | exact superpose eq1315 eq3290
    | exact resolve eq3290 eq1315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315 eq3290
  have eq3394 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3384 X0 X1
       have i₂ := eq592 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq592 eq3384
    | exact resolve eq3384 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3384
  have eq3399 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3394 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq3394
    | exact resolve eq3394 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3394
  have eq3904 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq3399 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3399
    | (have j0 := eq3399 x y
       grind)
    | exact resolve eq3399 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3910 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq3399
    | (have j0 := eq3399 (σ x) (σ y)
       grind)
    | exact resolve eq3399 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4057 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op (M.op x y) x) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq3904 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq3904
       grind)
    | exact resolve eq12 eq3904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3904
  have eq4074 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (k x (M.op x y)) := by grind
  clear eq4057
  have eq4226 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3910 eq12
    | (have j0 := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq3910
       grind)
    | exact resolve eq12 eq3910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3910
  have eq4243 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq4226
  have eq4656 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) y) := by
    intro X1
    first
    | exact superpose eq1536 eq243
    | (have j0 := eq243 y X1
       grind)
    | exact resolve eq243 eq1536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq4657 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) y) := by
    intro X1
    first
    | exact superpose eq2171 eq4656
    | exact resolve eq4656 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4656
  have eq4814 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3282 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq3282 X0 X1
       grind)
    | exact superpose eq3282 eq3282
    | exact resolve eq3282 eq3282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4822 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq4657 eq3282
    | exact resolve eq3282 eq4657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4657
  have eq4885 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3399 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq3282 X0 X1
       grind)
    | exact superpose eq3282 eq3399
    | exact resolve eq3399 eq3282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3399
  have eq4886 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4885 X0 X1
       have i₂ := eq592 (M.op X0 X1) X1 X1
       grind)
    | exact superpose eq592 eq4885
    | exact resolve eq4885 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4885
  have eq4927 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op x (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq2317 eq4822
    | exact resolve eq4822 eq2317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4822
  have eq4931 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4814 X0 X1
       have i₂ := eq1338 X0 (M.op X0 X1)
       grind)
    | exact superpose eq1338 eq4814
    | exact resolve eq4814 eq1338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4814
  have eq4945 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4886 X0 X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq4886
    | exact resolve eq4886 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4886
  have eq4971 : ∀ X0 : G, (M.op x x) = (M.op x (M.op (M.op (M.op x y) x) X0)) := by
    intro X0
    first
    | exact superpose eq2551 eq4927
    | exact resolve eq4927 eq2551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2551 eq4927
  have eq4973 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4931 X0 X1
       have i₂ := eq592 X0 X0 X1
       grind)
    | exact superpose eq592 eq4931
    | exact resolve eq4931 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4931
  have eq5407 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1781 eq252
    | (have j0 := eq252 (σ y) X1
       grind)
    | exact resolve eq252 eq1781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq5408 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq2165 eq5407
    | exact resolve eq5407 eq2165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5407
  have eq5488 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq5408 eq3282
    | exact resolve eq3282 eq5408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5408
  have eq5494 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq2218 eq5488
    | exact resolve eq5488 eq2218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5488
  have eq5504 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq2550 eq5494
    | exact resolve eq5494 eq2550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2550 eq5494
  have eq8001 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4973 X0 X2
       have i₂ := eq4973 X0 X1
       grind)
    | (have i₁ := eq4973 X1 X1
       have i₂ := eq4973 X1 X1
       grind)
    | exact superpose eq4973 eq4973
    | exact resolve eq4973 eq4973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8067 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1303 X0 X2
       have i₂ := eq4973 X0 X1
       grind)
    | (have i₁ := eq1303 X1 X1
       have i₂ := eq4973 X1 X1
       grind)
    | exact superpose eq4973 eq1303
    | exact resolve eq1303 eq4973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1303 eq4973
  have eq10205 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq912 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq912
    | (have j0 := eq912 x
       grind)
    | exact resolve eq912 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq10243 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10205
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq10205
    | exact resolve eq10205 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10205
  have eq10263 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | exact superpose eq26 eq10243
    | exact resolve eq10243 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10243
  have eq10276 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | exact superpose eq26 eq10263
    | exact resolve eq10263 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10263
  have eq10286 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq10276
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq10276
    | exact resolve eq10276 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10276
  have eq10294 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq10286
    | exact resolve eq10286 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10286
  have eq14257 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1536 eq571
    | (have j0 := eq571 y X1 X2
       grind)
    | exact resolve eq571 eq1536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571 eq1536
  have eq14258 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) x) X1)) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq2171 eq14257
    | exact resolve eq14257 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14257
  have eq14259 : ∀ X2 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x x) X2)) y) := by
    intro X2
    first
    | exact superpose eq4971 eq14258
    | exact resolve eq14258 eq4971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4971 eq14258
  have eq14265 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x y) (M.op x X0))) y) := by
    intro X0
    first
    | (have i₁ := eq14259 y
       have i₂ := eq1194 X0
       grind)
    | exact superpose eq1194 eq14259
    | exact resolve eq14259 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194 eq14259
  have eq14322 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) y) := by
    first
    | (have i₁ := eq14265 x
       have i₂ := eq592 sF0 x (M.op x x)
       grind)
    | exact superpose eq592 eq14265
    | exact resolve eq14265 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14265
  have eq14346 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) y) := by
    first
    | (have i₁ := eq14322
       have i₂ := eq1338 sF0 x
       grind)
    | exact superpose eq1338 eq14322
    | exact resolve eq14322 eq1338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14322
  have eq14363 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) x) y) := by
    first
    | exact superpose eq2351 eq14346
    | exact resolve eq14346 eq2351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14346
  have eq14440 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1781 eq572
    | (have j0 := eq572 (σ y) X1 X2
       grind)
    | exact resolve eq572 eq1781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq1781
  have eq14441 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq2165 eq14440
    | exact resolve eq14440 eq2165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14440
  have eq14442 : ∀ X2 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ x)) X2)) (σ y)) := by
    intro X2
    first
    | exact superpose eq5504 eq14441
    | exact resolve eq14441 eq5504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5504 eq14441
  have eq14448 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) (σ y)) := by
    intro X0
    first
    | exact superpose eq1195 eq14442
    | exact resolve eq14442 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195 eq14442
  have eq14505 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq14448 x
       have i₂ := eq592 sF4 sF2 (M.op sF2 x)
       grind)
    | exact superpose eq592 eq14448
    | exact resolve eq14448 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14448
  have eq14529 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq14505
       have i₂ := eq1338 sF4 sF2
       grind)
    | exact superpose eq1338 eq14505
    | exact resolve eq14505 eq1338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338 eq14505
  have eq14546 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) (σ y)) := by
    first
    | exact superpose eq2250 eq14529
    | exact resolve eq14529 eq2250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14529
  have eq14562 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14546
       have i₂ := eq8001 sF4 sF2 x
       grind)
    | (have i₁ := eq14546
       have i₂ := eq8001 sF4 x sF2
       grind)
    | exact superpose eq8001 eq14546
    | exact resolve eq14546 eq8001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8001 eq14546
  have eq21359 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) X3) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq580 X0 X1 x X3 X4
       have i₂ := eq592 X0 X1 x
       grind)
    | exact superpose eq592 eq580
    | exact resolve eq580 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq21479 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) (M.op (M.op X0 X0) (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21359 X0 (M.op X0 X1) X2 X2
       have i₂ := eq55 X0 X0 X1 X2
       grind)
    | exact superpose eq55 eq21359
    | exact resolve eq21359 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq21359
  have eq21594 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21479 X0 X1 X2
       have i₂ := eq592 (M.op X0 X0) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq592 eq21479
    | exact resolve eq21479 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21479
  have eq21714 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21594 X0 X1 X2
       have i₂ := eq592 X0 X0 X0
       grind)
    | exact superpose eq592 eq21594
    | exact resolve eq21594 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21594
  have eq21793 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21714 X0 X1 X2
       have i₂ := eq8067 X0 X0 X1
       grind)
    | exact superpose eq8067 eq21714
    | exact resolve eq21714 eq8067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8067 eq21714
  have eq21838 : ∀ X0 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X0) X0) X2) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq21793 X0 x X2
       have i₂ := eq592 X0 X0 x
       grind)
    | exact superpose eq592 eq21793
    | exact resolve eq21793 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21793
  have eq41513 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) X5)) X3) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq701 X0 X1 x X3 X4 X5
       have i₂ := eq592 X0 X1 x
       grind)
    | exact superpose eq592 eq701
    | exact resolve eq701 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592 eq701
  have eq47401 : x = (M.op (M.op x x) y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq4074 eq2317
    | exact resolve eq2317 eq4074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4074
  have eq47523 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq47401
       have i₂ := eq1476
       grind)
    | exact superpose eq1476 eq47401
    | exact resolve eq47401 eq1476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476 eq47401
  have eq47538 : x = (k x (M.op x y)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq2171 eq47523
    | exact resolve eq47523 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2171 eq47523
  have eq49097 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq4243 eq2218
    | exact resolve eq2218 eq4243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4243
  have eq49207 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1721 eq49097
    | exact resolve eq49097 eq1721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1721 eq49097
  have eq49223 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq2165 eq49207
    | exact resolve eq49207 eq2165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2165 eq49207
  have eq61758 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) X2)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) (M.op X0 (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) X2))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41513 X0 X0 X1 X2 X0
       have i₂ := eq21838 X0 (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) X2)
       grind)
    | exact superpose eq21838 eq41513
    | exact resolve eq41513 eq21838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41513
  have eq61814 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) = (M.op (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X0 X1) X2))) X1) := by
    intro X0 X1 X2
    by_contra hcon
    push Not at hcon
    have f61814_12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) X2)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) (M.op X0 (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) X2))) X1) := by
      intro X0 X1 X2
      grind
    have f61814_13 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) = (M.op X0 X1) := by
      intro X0 X1
      grind
    have f61814_19 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X0 := by
      intro X0 X1 X2
      grind
    have f61814_22 : (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) ≠ (M.op (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X0 X1) X2))) X1) := by grind
    have f61814_23 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) = (M.op (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X0 X1) X2))) X1) := by
      intro X0 X1 X2
      first
      | (have i₁ := f61814_12 X0 X1 X2
         have i₂ := f61814_13 X0 X1
         grind)
      | exact superpose f61814_13 f61814_12
      | exact resolve f61814_12 f61814_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f61814_24 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) = X0 := by
      intro X0 X1 X2
      first
      | (have i₁ := f61814_23 X0 X1 X2
         have i₂ := f61814_19 X0 X1 (M.op (M.op X0 X1) X2)
         grind)
      | exact superpose f61814_19 f61814_23
      | exact resolve f61814_23 f61814_19
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f61814_191 : X0 ≠ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) := by
      first
      | (have i₁ := f61814_22
         have i₂ := f61814_19 X0 X1 (M.op (M.op X0 X1) X2)
         grind)
      | exact superpose f61814_19 f61814_22
      | exact resolve f61814_22 f61814_19
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f61814_192 : False := by
      first
      | (have r₁ := f61814_191
         have r₂ := f61814_24 X0 X1 X2
         grind)
      | exact resolve f61814_191 f61814_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f61814_192
  clear eq21838 eq61758
  have eq61917 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61814 X0 X1 X2
       have i₂ := eq14 X0 X1 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq14 eq61814
    | exact resolve eq61814 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61814
  have eq80588 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq80589 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq80588
    | exact resolve eq80588 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80588
  have eq80600 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq80589
       have r₂ := eq27
       grind)
    | exact resolve eq80589 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80589
  have eq80604 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq80600
    | exact resolve eq80600 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80600
  have eq80608 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq80604
    | exact resolve eq80604 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80604
  have eq80626 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq80608 eq3282
    | exact resolve eq3282 eq80608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80608
  have eq80643 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq2250 eq80626
    | exact resolve eq80626 eq2250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2250 eq80626
  have eq88888 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq80643 eq61917
    | exact resolve eq61917 eq80643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61917 eq80643
  have eq88942 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq14562 eq88888
    | exact resolve eq88888 eq14562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14562 eq88888
  have eq88943 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq88942
  have eq88975 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq88943 eq79
    | (have r₁ := eq79
       have r₂ := eq88943
       grind)
    | exact resolve eq79 eq88943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq88943
  have eq89125 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq88975
  have eq112625 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq89125 eq4945
    | exact resolve eq4945 eq89125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89125
  have eq112638 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq2218 eq112625
    | exact resolve eq112625 eq2218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112625
  have eq112981 : (τ (σ x)) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq112638 eq59
    | exact resolve eq59 eq112638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq112638
  have eq113003 : x = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq28 eq112981
    | exact resolve eq112981 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112981
  have eq113010 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have r₁ := eq113003
       have r₂ := eq78
       grind)
    | exact resolve eq113003 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq113003
  have eq113014 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq113010
       grind)
    | exact superpose eq113010 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq113010
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq113010
       grind)
    | exact resolve eq13 eq113010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113029 : y = (M.op (M.op (M.op x y) x) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq3282 y x
       have i₂ := eq113010
       grind)
    | exact superpose eq113010 eq3282
    | exact resolve eq3282 eq113010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3282 eq113010
  have eq113048 : y = (M.op (M.op (M.op x y) x) x) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | exact superpose eq2351 eq113029
    | exact resolve eq113029 eq2351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2351 eq113029
  have eq113054 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have r₁ := eq113014
       have r₂ := eq18
       grind)
    | exact resolve eq113014 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113014
  have eq113825 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | exact superpose eq113048 eq14363
    | exact resolve eq14363 eq113048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14363 eq113048
  have eq116976 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq113054
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq113054
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq113054 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113054
  have eq116992 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq116976
  have eq117004 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq116992
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116992
    | exact resolve eq116992 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116992
  have eq117007 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq117004
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117004
    | exact resolve eq117004 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117004
  have eq117009 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq117007
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117007
    | exact resolve eq117007 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117007
  have eq119364 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x x)) X0) X0) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq1301 y X0
       have i₂ := eq113825
       grind)
    | exact superpose eq113825 eq1301
    | exact resolve eq1301 eq113825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113825
  have eq119481 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq119364 x
       have i₂ := eq1301 x x
       grind)
    | exact superpose eq1301 eq119364
    | exact resolve eq119364 eq1301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1301 eq119364
  have eq119528 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq119481
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq119481
    | exact resolve eq119481 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119481
  have eq119543 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq119528
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq119528
    | exact resolve eq119528 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119528
  have eq119544 : x = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq119543
  have eq119553 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq119544
       grind)
    | exact superpose eq119544 eq44
    | exact resolve eq44 eq119544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq119544
  have eq119575 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq119553
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq119553
    | exact resolve eq119553 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119553
  have eq119584 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10294 eq119575
    | exact resolve eq119575 eq10294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10294 eq119575
  have eq174545 : y = (M.op (M.op (M.op x y) x) y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4945 y x
       have i₂ := eq117009
       grind)
    | exact superpose eq117009 eq4945
    | exact resolve eq4945 eq117009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117009
  have eq174559 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2317 eq174545
    | exact resolve eq174545 eq2317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2317 eq174545
  have eq174579 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq174559
       grind)
    | exact superpose eq174559 eq73
    | exact resolve eq73 eq174559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174559
  have eq174847 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq174579
    | exact resolve eq174579 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174579
  have eq208552 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq119584 eq4945
    | exact resolve eq4945 eq119584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4945 eq119584
  have eq208566 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2218 eq208552
    | exact resolve eq208552 eq2218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2218 eq208552
  have eq208567 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq208566
  have eq208653 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq208567 eq174847
    | exact resolve eq174847 eq208567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208786 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq208653
  have eq208855 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq208786
       have r₂ := eq27
       grind)
    | exact resolve eq208786 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208786
  have eq209507 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq208855 eq27
    | exact resolve eq27 eq208855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209585 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq208855 eq49223
    | exact resolve eq49223 eq208855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49223 eq208855
  have eq209787 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq209585
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq209585
    | exact resolve eq209585 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209585
  have eq209788 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq209787
  have eq218536 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq209788 eq174847
    | exact resolve eq174847 eq209788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174847 eq209788
  have eq218681 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq218536
  have eq218772 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq218681
       have r₂ := eq209507
       grind)
    | exact resolve eq218681 eq209507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209507 eq218681
  have eq219158 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq218772 eq29
    | exact resolve eq29 eq218772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218772
  have eq219397 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq219158
    | exact resolve eq219158 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219158
  have eq219398 : x = (M.op x y) ∨ x = y := by grind
  clear eq219397
  have eq219432 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq219398 eq20
    | exact resolve eq20 eq219398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219642 : x = (k x x) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq219398 eq47538
    | exact resolve eq47538 eq219398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47538 eq219398
  have eq219770 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq219642
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq219642
    | exact resolve eq219642 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq219642
  have eq219771 : x = (M.op x x) ∨ x = y := by grind
  clear eq219770
  have eq219940 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq219432
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq219432
    | exact resolve eq219432 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219432
  have eq220487 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq219771
       grind)
    | exact superpose eq219771 eq73
    | exact resolve eq73 eq219771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq219771
  have eq220798 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq220487
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq220487
    | exact resolve eq220487 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220487
  have eq223762 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq220798 eq208567
    | exact resolve eq208567 eq220798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208567 eq220798
  have eq223905 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq223762
  have eq228938 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq223905 eq27
    | exact resolve eq27 eq223905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223905
  have eq229330 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq228938
       have r₂ := eq219940
       grind)
    | exact resolve eq228938 eq219940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219940 eq228938
  have eq229652 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq229330 eq29
    | exact resolve eq29 eq229330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq229330
  have eq229893 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq229652
    | exact resolve eq229652 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq229652
  have eq229894 : x = y := by grind
  clear eq229893
  have eq229931 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq229894
       grind)
    | exact superpose eq229894 eq18
    | exact resolve eq18 eq229894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq229932 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq229894
       grind)
    | exact superpose eq229894 eq24
    | exact resolve eq24 eq229894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq229894
  have eq230424 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq229932
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq229932
    | exact resolve eq229932 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq229932
  have eq230498 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq230424 eq26
    | exact resolve eq26 eq230424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq230424
  have eq231199 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq230498 eq72
    | exact resolve eq72 eq230498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq230498
  have eq231481 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq231199
       have i₂ := eq229931
       grind)
    | exact superpose eq229931 eq231199
    | exact resolve eq231199 eq229931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229931 eq231199
  have eq231607 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq231481 eq15
    | exact resolve eq15 eq231481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231481
  have eq231958 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq231607
    | exact resolve eq231607 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq231607
  have eq232069 : False := by grind
  exact eq232069

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,X) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_y_pxx_x_pyx_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X3 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq10
    | exact resolve eq10 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq43
    | exact resolve eq43 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq71 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq49
    | exact resolve eq49 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq71
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq71
    | exact resolve eq71 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq73 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq70
    | exact resolve eq70 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq69
    | exact resolve eq69 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq103 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq103
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq103
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq103 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
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
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq118
    | exact resolve eq118 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq119
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119
    | exact resolve eq119 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq239 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
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
  have eq244 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq67 (τ X0)
       grind)
    | exact superpose eq67 eq34
    | exact resolve eq34 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq298 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq287 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq287
    | exact resolve eq287 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq300 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq298 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq298
    | exact resolve eq298 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq298
  have eq576 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) X2)) y) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq577 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) X2)) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq585 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) X3) := by
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
  have eq597 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
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
  have eq708 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) X5)) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3 X2 X3
       have i₂ := eq55 X0 X1 X2 X3
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq727 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq16
    | exact resolve eq16 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq1185 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x x) y) := by
    intro X0
    first
    | (have i₁ := eq597 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq597
    | (have j0 := eq597 x y X0
       grind)
    | exact resolve eq597 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1186 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq597
    | (have j0 := eq597 (σ x) (σ y) X0
       grind)
    | exact resolve eq597 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1201 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq597 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq597
    | (have j0 := eq597 x X0 y
       grind)
    | exact resolve eq597 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1202 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq597
    | (have j0 := eq597 (σ x) X0 (σ y)
       grind)
    | exact resolve eq597 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1208 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq597 X0 X1 x
       grind)
    | exact superpose eq597 eq14
    | exact resolve eq14 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1292 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1208 X0 (M.op X0 X1)
       have i₂ := eq597 X0 X0 X1
       grind)
    | exact superpose eq597 eq1208
    | exact resolve eq1208 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1293 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1208 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq1208 X0 (M.op X0 X0)
       grind)
    | exact superpose eq1208 eq1208
    | exact resolve eq1208 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1297 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1 X1 X0
       have i₂ := eq1208 (M.op X0 X1) X0
       grind)
    | exact superpose eq1208 eq55
    | exact resolve eq55 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1304 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X1
       have i₂ := eq1208 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq1208 eq14
    | exact resolve eq14 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1328 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1297 X0 X1
       have i₂ := eq597 X0 X1 X1
       grind)
    | exact superpose eq597 eq1297
    | exact resolve eq1297 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297
  have eq1338 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1293 (σ X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq1293
    | exact resolve eq1293 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1339 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1293 (τ X0)
       have i₂ := eq727 X0
       grind)
    | exact superpose eq727 eq1293
    | exact resolve eq1293 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727 eq1293
  have eq1468 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq1201 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1201
    | (have j0 := eq1201 y
       grind)
    | exact resolve eq1201 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1528 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1468
       have i₂ := eq1185 X0
       grind)
    | exact superpose eq1185 eq1468
    | exact resolve eq1468 eq1185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1712 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq26 eq1202
    | (have j0 := eq1202 (σ y)
       grind)
    | exact resolve eq1202 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202
  have eq1772 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1186 eq1712
    | exact resolve eq1712 eq1186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2105 : (M.op x x) = (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op x x)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1292 (M.op x x) y
       have i₂ := eq1468
       grind)
    | exact superpose eq1468 eq1292
    | exact resolve eq1292 eq1468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2109 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) x) := by
    first
    | exact superpose eq239 eq1292
    | exact resolve eq1292 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2111 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1712 eq1292
    | exact resolve eq1292 eq1712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2115 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq250 eq1292
    | exact resolve eq1292 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2155 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq2115
       have i₂ := eq1208 sF4 (M.op sF4 sF4)
       grind)
    | exact superpose eq1208 eq2115
    | exact resolve eq2115 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2115
  have eq2159 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq2111
       have i₂ := eq1208 sF2 (M.op sF2 sF2)
       grind)
    | exact superpose eq1208 eq2111
    | exact resolve eq2111 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2111
  have eq2161 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq2109
       have i₂ := eq1208 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq1208 eq2109
    | exact resolve eq2109 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2109
  have eq2165 : (M.op x x) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq2105
       have i₂ := eq1208 x (M.op x x)
       grind)
    | exact superpose eq1208 eq2105
    | exact resolve eq2105 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2105
  have eq2207 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq2155 eq250
    | exact resolve eq250 eq2155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2220 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2155 eq597
    | exact resolve eq597 eq2155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2231 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq2220 x
       have i₂ := eq597 sF4 sF2 x
       grind)
    | exact superpose eq597 eq2220
    | exact resolve eq2220 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2220
  have eq2238 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq2155 eq2231
    | exact resolve eq2231 eq2155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2231
  have eq2304 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq2161 eq239
    | exact resolve eq239 eq2161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2318 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2161 eq597
    | exact resolve eq597 eq2161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2330 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | (have i₁ := eq2318 x
       have i₂ := eq597 sF0 x x
       grind)
    | exact superpose eq597 eq2318
    | exact resolve eq2318 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2318
  have eq2337 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq2161 eq2330
    | exact resolve eq2330 eq2161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2330
  have eq2535 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq2155 eq2159
    | exact resolve eq2159 eq2155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2159
  have eq2536 : (M.op x x) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq2161 eq2165
    | exact resolve eq2165 eq2161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2165
  have eq3270 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1328 (M.op X0 X1) X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq1328
    | exact resolve eq1328 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3272 : x = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | exact superpose eq239 eq1328
    | exact resolve eq1328 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq3274 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq250 eq1328
    | exact resolve eq1328 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3278 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1328 (M.op (M.op X0 X0) X0) (M.op X0 X1)
       have i₂ := eq1292 X0 X1
       grind)
    | exact superpose eq1292 eq1328
    | exact resolve eq1328 eq1292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3300 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1208 X0 X1
       have i₂ := eq1328 X0 X1
       grind)
    | (have i₁ := eq1208 X1 X1
       have i₂ := eq1328 X1 X1
       grind)
    | exact superpose eq1328 eq1208
    | exact resolve eq1208 eq1328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq3372 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3278 X0 X1
       have i₂ := eq1304 X0 X0
       grind)
    | exact superpose eq1304 eq3278
    | exact resolve eq3278 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304 eq3278
  have eq3382 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3372 X0 X1
       have i₂ := eq597 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq597 eq3372
    | exact resolve eq3372 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3372
  have eq3387 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3382 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq3382
    | exact resolve eq3382 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3382
  have eq3886 : (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq3274 eq3387
    | exact resolve eq3387 eq3274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3274
  have eq3964 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq3886
       have i₂ := eq597 sF4 sF3 sF3
       grind)
    | exact superpose eq597 eq3886
    | exact resolve eq3886 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3886
  have eq4003 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) := by
    first
    | exact superpose eq250 eq3964
    | exact resolve eq3964 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq3964
  have eq4639 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) y) := by
    intro X1
    first
    | exact superpose eq1528 eq244
    | (have j0 := eq244 y X1
       grind)
    | exact resolve eq244 eq1528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq4640 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) y) := by
    intro X1
    first
    | exact superpose eq2161 eq4639
    | exact resolve eq4639 eq2161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4639
  have eq4796 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3270 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq3270 X0 X1
       grind)
    | exact superpose eq3270 eq3270
    | exact resolve eq3270 eq3270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4804 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq4640 eq3270
    | exact resolve eq3270 eq4640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4640
  have eq4813 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq3272 eq3270
    | exact resolve eq3270 eq3272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3272
  have eq4868 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3387 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq3270 X0 X1
       grind)
    | exact superpose eq3270 eq3387
    | exact resolve eq3387 eq3270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4869 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4868 X0 X1
       have i₂ := eq597 (M.op X0 X1) X1 X1
       grind)
    | exact superpose eq597 eq4868
    | exact resolve eq4868 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4868
  have eq4903 : (M.op (M.op x y) y) = (M.op (M.op x x) (M.op x y)) := by
    first
    | (have i₁ := eq4813
       have i₂ := eq1328 x sF0
       grind)
    | exact superpose eq1328 eq4813
    | exact resolve eq4813 eq1328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4813
  have eq4911 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op x (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq2304 eq4804
    | exact resolve eq4804 eq2304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4804
  have eq4915 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4796 X0 X1
       have i₂ := eq1328 X0 (M.op X0 X1)
       grind)
    | exact superpose eq1328 eq4796
    | exact resolve eq4796 eq1328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4796
  have eq4929 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4869 X0 X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq4869
    | exact resolve eq4869 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4869
  have eq4952 : (M.op (M.op x y) y) = (M.op (M.op x x) x) := by
    first
    | exact superpose eq1201 eq4903
    | exact resolve eq4903 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201 eq4903
  have eq4956 : ∀ X0 : G, (M.op x x) = (M.op x (M.op (M.op (M.op x y) x) X0)) := by
    intro X0
    first
    | exact superpose eq2536 eq4911
    | exact resolve eq4911 eq2536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2536 eq4911
  have eq4958 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4915 X0 X1
       have i₂ := eq597 X0 X0 X1
       grind)
    | exact superpose eq597 eq4915
    | exact resolve eq4915 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4915
  have eq5397 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1772 eq255
    | (have j0 := eq255 (σ y) X1
       grind)
    | exact resolve eq255 eq1772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq5398 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq2155 eq5397
    | exact resolve eq5397 eq2155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5397
  have eq5478 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq5398 eq3270
    | exact resolve eq3270 eq5398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5398
  have eq5484 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq2207 eq5478
    | exact resolve eq5478 eq2207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2207 eq5478
  have eq5494 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq2535 eq5484
    | exact resolve eq5484 eq2535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2535 eq5484
  have eq7995 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4958 X0 X2
       have i₂ := eq4958 X0 X1
       grind)
    | (have i₁ := eq4958 X1 X1
       have i₂ := eq4958 X1 X1
       grind)
    | exact superpose eq4958 eq4958
    | exact resolve eq4958 eq4958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8006 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq4958 x X0
       have i₂ := eq4952
       grind)
    | exact superpose eq4952 eq4958
    | exact resolve eq4958 eq4952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4952
  have eq8061 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1292 X0 X2
       have i₂ := eq4958 X0 X1
       grind)
    | (have i₁ := eq1292 X1 X1
       have i₂ := eq4958 X1 X1
       grind)
    | exact superpose eq4958 eq1292
    | exact resolve eq1292 eq4958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292
  have eq15319 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1528 eq576
    | (have j0 := eq576 y X1 X2
       grind)
    | exact resolve eq576 eq1528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq1528
  have eq15320 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) x) X1)) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq2161 eq15319
    | exact resolve eq15319 eq2161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15319
  have eq15321 : ∀ X2 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x x) X2)) y) := by
    intro X2
    first
    | exact superpose eq4956 eq15320
    | exact resolve eq15320 eq4956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4956 eq15320
  have eq15445 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x y) (M.op x X0))) y) := by
    intro X0
    first
    | (have i₁ := eq15321 y
       have i₂ := eq1185 X0
       grind)
    | exact superpose eq1185 eq15321
    | exact resolve eq15321 eq1185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185 eq15321
  have eq15503 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) y) := by
    first
    | (have i₁ := eq15445 x
       have i₂ := eq597 sF0 x (M.op x x)
       grind)
    | exact superpose eq597 eq15445
    | exact resolve eq15445 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15445
  have eq15528 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) y) := by
    first
    | (have i₁ := eq15503
       have i₂ := eq1328 sF0 x
       grind)
    | exact superpose eq1328 eq15503
    | exact resolve eq15503 eq1328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15503
  have eq15546 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) x) y) := by
    first
    | exact superpose eq2337 eq15528
    | exact resolve eq15528 eq2337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2337 eq15528
  have eq15563 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) X0) X0) y) := by
    intro X0
    first
    | (have i₁ := eq15546
       have i₂ := eq7995 sF0 x x
       grind)
    | (have i₁ := eq15546
       have i₂ := eq7995 sF0 x x
       grind)
    | exact superpose eq7995 eq15546
    | exact resolve eq15546 eq7995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15546
  have eq15625 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1772 eq577
    | (have j0 := eq577 (σ y) X1 X2
       grind)
    | exact resolve eq577 eq1772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577 eq1772
  have eq15626 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq2155 eq15625
    | exact resolve eq15625 eq2155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15625
  have eq15627 : ∀ X2 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ x)) X2)) (σ y)) := by
    intro X2
    first
    | exact superpose eq5494 eq15626
    | exact resolve eq15626 eq5494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5494 eq15626
  have eq15733 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) (σ y)) := by
    intro X0
    first
    | exact superpose eq1186 eq15627
    | exact resolve eq15627 eq1186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186 eq15627
  have eq15791 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq15733 x
       have i₂ := eq597 sF4 sF2 (M.op sF2 x)
       grind)
    | exact superpose eq597 eq15733
    | exact resolve eq15733 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15733
  have eq15816 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq15791
       have i₂ := eq1328 sF4 sF2
       grind)
    | exact superpose eq1328 eq15791
    | exact resolve eq15791 eq1328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328 eq15791
  have eq15834 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) (σ y)) := by
    first
    | exact superpose eq2238 eq15816
    | exact resolve eq15816 eq2238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2238 eq15816
  have eq15851 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15834
       have i₂ := eq7995 sF4 sF2 x
       grind)
    | (have i₁ := eq15834
       have i₂ := eq7995 sF4 x sF2
       grind)
    | exact superpose eq7995 eq15834
    | exact resolve eq15834 eq7995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7995 eq15834
  have eq22519 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) X3) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq585 X0 X1 x X3 X4
       have i₂ := eq597 X0 X1 x
       grind)
    | exact superpose eq597 eq585
    | exact resolve eq585 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq22796 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) (M.op (M.op X0 X0) (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22519 X0 (M.op X0 X1) X2 X2
       have i₂ := eq55 X0 X0 X1 X2
       grind)
    | exact superpose eq55 eq22519
    | exact resolve eq22519 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq22519
  have eq22911 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22796 X0 X1 X2
       have i₂ := eq597 (M.op X0 X0) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq597 eq22796
    | exact resolve eq22796 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22796
  have eq23036 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22911 X0 X1 X2
       have i₂ := eq597 X0 X0 X0
       grind)
    | exact superpose eq597 eq22911
    | exact resolve eq22911 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22911
  have eq23120 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23036 X0 X1 X2
       have i₂ := eq8061 X0 X0 X1
       grind)
    | exact superpose eq8061 eq23036
    | exact resolve eq23036 eq8061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23036
  have eq23167 : ∀ X0 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X0) X0) X2) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq23120 X0 x X2
       have i₂ := eq597 X0 X0 x
       grind)
    | exact superpose eq597 eq23120
    | exact resolve eq23120 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23120
  have eq42020 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) X5)) X3) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq708 X0 X1 x X3 X4 X5
       have i₂ := eq597 X0 X1 x
       grind)
    | exact superpose eq597 eq708
    | exact resolve eq708 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597 eq708
  have eq59946 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) X2)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) (M.op X0 (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) X2))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42020 X0 X0 X1 X2 X0
       have i₂ := eq23167 X0 (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) X2)
       grind)
    | exact superpose eq23167 eq42020
    | exact resolve eq42020 eq23167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42020
  have eq60004 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) = (M.op (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X0 X1) X2))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59946 X0 X2 X2
       have i₂ := eq23167 X0 X2
       grind)
    | exact superpose eq23167 eq59946
    | exact resolve eq59946 eq23167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23167 eq59946
  have eq60111 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60004 X0 X1 X2
       have i₂ := eq14 X0 X1 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq14 eq60004
    | exact resolve eq60004 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60004
  have eq66193 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1338 (M.op (M.op x x) x)
       have i₂ := eq60111 x x x
       grind)
    | exact superpose eq60111 eq1338
    | exact resolve eq1338 eq60111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338
  have eq66194 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op (M.op X0 X0) X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1339 (M.op (M.op x x) x)
       have i₂ := eq60111 x x x
       grind)
    | exact superpose eq60111 eq1339
    | exact resolve eq1339 eq60111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339 eq60111
  have eq67308 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X1) X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq66193 X0
       have i₂ := eq4958 X0 X1
       grind)
    | (have i₁ := eq66193 X1
       have i₂ := eq4958 X1 X1
       grind)
    | exact superpose eq4958 eq66193
    | exact resolve eq66193 eq4958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66193
  have eq67868 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op (M.op X0 X1) X1)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq66194 X0
       have i₂ := eq4958 X0 X1
       grind)
    | (have i₁ := eq66194 X1
       have i₂ := eq4958 X1 X1
       grind)
    | exact superpose eq4958 eq66194
    | exact resolve eq66194 eq4958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4958 eq66194
  have eq80217 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq120 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq80218 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq80217
    | exact resolve eq80217 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80217
  have eq80229 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq80218
       have r₂ := eq27
       grind)
    | exact resolve eq80218 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80218
  have eq80233 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq80229
    | exact resolve eq80229 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80229
  have eq80256 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq80233 eq3300
    | exact resolve eq3300 eq80233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3300 eq80233
  have eq80272 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq4003 eq80256
    | exact resolve eq80256 eq4003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4003 eq80256
  have eq80315 : (τ (σ y)) = (M.op (τ (M.op (σ x) (σ x))) (τ (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq80272 eq67868
    | exact resolve eq67868 eq80272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67868 eq80272
  have eq80318 : y = (M.op (τ (M.op (σ x) (σ x))) y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq80315
    | exact resolve eq80315 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80315
  have eq80333 : y = (M.op (M.op x x) y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq72 eq80318
    | exact resolve eq80318 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80318
  have eq80338 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq80333
       have i₂ := eq1468
       grind)
    | exact superpose eq1468 eq80333
    | exact resolve eq80333 eq1468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468 eq80333
  have eq80340 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2161 eq80338
    | exact resolve eq80338 eq2161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2161 eq80338
  have eq81229 : y = (M.op (M.op (M.op x y) x) y) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq4929 y x
       have i₂ := eq80340
       grind)
    | exact superpose eq80340 eq4929
    | exact resolve eq4929 eq80340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4929 eq80340
  have eq81242 : y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq2304 eq81229
    | exact resolve eq81229 eq2304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81229
  have eq81526 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq81242 eq2304
    | exact resolve eq2304 eq81242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2304 eq81242
  have eq81748 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq3387 y y
       have i₂ := eq81526
       grind)
    | exact superpose eq81526 eq3387
    | exact resolve eq3387 eq81526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3387 eq81526
  have eq81760 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq81748
  have eq81858 : y = (M.op (M.op x x) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3270 y x
       have i₂ := eq81760
       grind)
    | exact superpose eq81760 eq3270
    | exact resolve eq3270 eq81760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3270
  have eq81871 : (σ y) = (M.op (σ (M.op x x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq67308 y x
       have i₂ := eq81760
       grind)
    | exact superpose eq81760 eq67308
    | exact resolve eq67308 eq81760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67308 eq81760
  have eq81875 : (σ y) = (M.op (σ (M.op x x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq81871
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq81871
    | exact resolve eq81871 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81871
  have eq81880 : y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq81858
       have i₂ := eq8006 x
       grind)
    | exact superpose eq8006 eq81858
    | exact resolve eq81858 eq8006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8006 eq81858
  have eq81890 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq81875
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq81875
    | exact resolve eq81875 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81875
  have eq81895 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1712 eq81890
    | exact resolve eq81890 eq1712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1712 eq81890
  have eq81897 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2155 eq81895
    | exact resolve eq81895 eq2155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2155 eq81895
  have eq81968 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) X0) X0) y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq81880 eq8061
    | exact resolve eq8061 eq81880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81880
  have eq81981 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq15563 eq81968
    | exact resolve eq81968 eq15563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15563 eq81968
  have eq82241 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq81897 eq8061
    | exact resolve eq8061 eq81897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8061 eq81897
  have eq82252 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq15851 eq82241
    | exact resolve eq82241 eq15851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15851 eq82241
  have eq82356 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq81981
       grind)
    | exact superpose eq81981 eq73
    | exact resolve eq73 eq81981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq81981
  have eq82578 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq82356
    | exact resolve eq82356 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82356
  have eq84050 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq82578 eq82252
    | exact resolve eq82252 eq82578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82252 eq82578
  have eq84169 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq84050
  have eq84201 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq84169
       have r₂ := eq27
       grind)
    | exact resolve eq84169 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84169
  have eq84230 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq84201 eq29
    | exact resolve eq29 eq84201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq84201
  have eq84424 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq84230
    | exact resolve eq84230 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq84230
  have eq84425 : x = y := by grind
  clear eq84424
  have eq84458 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq84425
       grind)
    | exact superpose eq84425 eq18
    | exact resolve eq18 eq84425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq84459 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq84425
       grind)
    | exact superpose eq84425 eq24
    | exact resolve eq24 eq84425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq84425
  have eq84659 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq84459
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq84459
    | exact resolve eq84459 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq84459
  have eq84689 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq84659 eq26
    | exact resolve eq26 eq84659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq84659
  have eq85246 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq84689 eq72
    | exact resolve eq72 eq84689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq84689
  have eq85477 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq85246
       have i₂ := eq84458
       grind)
    | exact superpose eq84458 eq85246
    | exact resolve eq85246 eq84458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84458 eq85246
  have eq85539 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq85477 eq15
    | exact resolve eq15 eq85477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85477
  have eq85635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq85539
    | exact resolve eq85539 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq85539
  have eq85663 : False := by grind
  exact eq85663

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_y_pxy_x_pxy_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X0 := by
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
  have eq54 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq43
    | exact resolve eq43 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq71 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq49
    | exact resolve eq49 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq71
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq71
    | exact resolve eq71 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq73 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq70
    | exact resolve eq70 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq79 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq95 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq93
       have i₂ := eq67 sF3
       grind)
    | exact superpose eq67 eq93
    | exact resolve eq93 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq97 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq95
       have i₂ := eq67 y
       grind)
    | exact superpose eq67 eq95
    | exact resolve eq95 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq86 x y
       grind)
    | exact superpose eq86 eq44
    | (have j1 := eq86 x y
       grind)
    | exact resolve eq44 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq125 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq128 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq125
    | exact resolve eq125 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq128
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq128
    | exact resolve eq128 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq149 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq152 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq149
       have i₂ := eq67 sF1
       grind)
    | exact superpose eq67 eq149
    | exact resolve eq149 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq154 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq152
       have i₂ := eq67 sF0
       grind)
    | exact superpose eq67 eq152
    | exact resolve eq152 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq152
  have eq175 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq154 eq16
    | exact resolve eq16 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq196 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129 eq86
    | (have j0 := eq86 (σ x) (σ y)
       grind)
    | exact resolve eq86 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq196
    | exact resolve eq196 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq200 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq197
       have r₂ := eq27
       grind)
    | exact resolve eq197 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq202 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq200
    | exact resolve eq200 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq255 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
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
  have eq266 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ x) X0)) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq202 eq51
    | exact resolve eq51 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq273 : (σ x) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq266
    | (have j0 := eq266 (σ y)
       grind)
    | exact resolve eq266 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq285 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq202 eq273
    | exact resolve eq273 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq291 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq285
  have eq307 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) X0) (σ y)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq202 eq54
    | exact resolve eq54 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq313 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq307
    | (have j0 := eq307 (σ y)
       grind)
    | exact resolve eq307 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq483 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq202 eq79
    | (have r₁ := eq79
       have r₂ := eq202
       grind)
    | exact resolve eq79 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq484 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq483
  have eq561 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq484 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq566 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq86 (σ x) (σ y)
       grind)
    | (have r₁ := eq561
       have r₂ := eq86 (σ x) (σ y)
       grind)
    | exact resolve eq561 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq561
  have eq569 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq566
    | exact resolve eq566 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq574 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129 eq569
    | exact resolve eq569 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq569
  have eq581 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq574
  have eq583 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq581
       have r₂ := eq27
       grind)
    | exact resolve eq581 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq593 : (M.op x x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq583 eq72
    | exact resolve eq72 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq630 : (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq175 eq593
    | exact resolve eq593 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq593
  have eq700 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
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
  clear eq52
  have eq1040 : x = (M.op (M.op x x) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq630 eq255
    | exact resolve eq255 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq1679 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq313 eq700
    | exact resolve eq700 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1828 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1679 X0
       have i₂ := eq14 sF4 sF3 sF3
       grind)
    | exact superpose eq14 eq1679
    | exact resolve eq1679 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1679
  have eq1903 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq313 eq1828
    | exact resolve eq1828 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313 eq1828
  have eq1924 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1903
  have eq1933 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1924 eq72
    | exact resolve eq72 eq1924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq1924
  have eq2092 : x = (M.op (τ (M.op (σ x) (σ y))) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1040
       have i₂ := eq1933
       grind)
    | exact superpose eq1933 eq1040
    | exact resolve eq1040 eq1933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040 eq1933
  have eq2112 : x = (M.op (τ (M.op (σ x) (σ y))) y) ∨ y = (M.op x y) := by grind
  clear eq2092
  have eq2143 : x = (M.op (τ (σ y)) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq202 eq2112
    | exact resolve eq2112 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq2112
  have eq2159 : x = (M.op (τ (σ y)) y) ∨ y = (M.op x y) := by grind
  clear eq2143
  have eq2160 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq2159
    | exact resolve eq2159 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2159
  have eq2205 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq2160
       grind)
    | exact superpose eq2160 eq97
    | exact resolve eq97 eq2160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq2160
  have eq2225 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2205
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2205
    | exact resolve eq2205 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2205
  have eq2229 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2225 eq291
    | exact resolve eq291 eq2225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291 eq2225
  have eq2255 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2229
  have eq2259 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2255
    | exact resolve eq2255 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2255
  have eq2262 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2259 eq27
    | exact resolve eq27 eq2259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2259
  have eq2310 : y = (M.op x y) := by
    first
    | (have r₁ := eq2262
       have r₂ := eq583
       grind)
    | exact resolve eq2262 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583 eq2262
  have eq2353 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2310 eq20
    | exact resolve eq20 eq2310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2362 : x = (M.op (M.op y y) y) := by
    first
    | exact superpose eq2310 eq255
    | exact resolve eq255 eq2310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq2310
  have eq2375 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2353
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2353
    | exact resolve eq2353 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353
  have eq2378 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2375 eq26
    | exact resolve eq26 eq2375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2477 : ∀ X0 : G, (M.op x (M.op (M.op y y) X0)) = (M.op (M.op (M.op y y) (M.op y y)) y) := by
    intro X0
    first
    | (have i₁ := eq700 (M.op y y) y X0
       have i₂ := eq2362
       grind)
    | exact superpose eq2362 eq700
    | exact resolve eq700 eq2362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2480 : ∀ X0 : G, y = (M.op x (M.op (M.op y y) X0)) := by
    intro X0
    first
    | (have i₁ := eq2477 X0
       have i₂ := eq14 y y y
       grind)
    | exact superpose eq14 eq2477
    | exact resolve eq2477 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2477
  have eq2843 : y = (M.op x x) := by
    first
    | (have i₁ := eq2480 y
       have i₂ := eq2362
       grind)
    | exact superpose eq2362 eq2480
    | exact resolve eq2480 eq2362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2362 eq2480
  have eq2869 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq2843
       grind)
    | exact superpose eq2843 eq73
    | exact resolve eq73 eq2843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq2843
  have eq2894 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2869
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2869
    | exact resolve eq2869 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2869
  have eq2895 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2375 eq2894
    | exact resolve eq2894 eq2375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2375 eq2894
  have eq2913 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq2895 eq14
    | exact resolve eq14 eq2895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2923 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq2895 eq700
    | exact resolve eq700 eq2895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3685 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq2895 eq2913
    | exact resolve eq2913 eq2895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2895 eq2913
  have eq3768 : (M.op (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2378 eq2923
    | (have j0 := eq2923 (σ y)
       grind)
    | exact resolve eq2923 eq2378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3777 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ (M.op x y)) X1)) (M.op (σ x) X0)) := by
    intro X0 X1
    first
    | exact superpose eq2923 eq14
    | exact resolve eq14 eq2923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2923
  have eq3793 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq3777 X0 x
       have i₂ := eq700 sF1 sF2 x
       grind)
    | exact superpose eq700 eq3777
    | exact resolve eq3777 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3777
  have eq3799 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq3685 eq3793
    | exact resolve eq3793 eq3685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3793
  have eq3808 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ (M.op x y)) X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq3768 eq14
    | exact resolve eq14 eq3768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3768
  have eq3824 : (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3808 x
       have i₂ := eq700 sF1 sF2 x
       grind)
    | exact superpose eq700 eq3808
    | exact resolve eq3808 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700 eq3808
  have eq3829 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3685 eq3824
    | exact resolve eq3824 eq3685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3685 eq3824
  have eq4056 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq3829 eq3799
    | exact resolve eq3799 eq3829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3799 eq3829
  have eq4087 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2378 eq4056
    | exact resolve eq4056 eq2378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2378 eq4056
  have eq4097 : False := by grind
  exact eq4097

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_pyy_pxy_y_pyx_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X3 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq10
    | exact resolve eq10 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq43
    | exact resolve eq43 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq71 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq49
    | exact resolve eq49 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq71
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq71
    | exact resolve eq71 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq73 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq70
    | exact resolve eq70 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq69
    | exact resolve eq69 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq78 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ x = (k y x) := by
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
  have eq79 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq101 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq101
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq101
       grind)
    | exact superpose eq101 eq16
    | exact resolve eq16 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq110
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq110
    | exact resolve eq110 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq116
    | exact resolve eq116 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq118 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
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
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq118
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq118
    | exact resolve eq118 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq239 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
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
  have eq243 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq572 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) X2)) y) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq593 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
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
  clear eq52
  have eq920 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq74 X1
       grind)
    | exact superpose eq74 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq972 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ X0) (σ y)) = (M.op (σ y) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq920 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq920
    | (have j0 := eq920 y X0
       grind)
    | exact resolve eq920 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq1189 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x x) y) := by
    intro X0
    first
    | (have i₁ := eq593 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq593
    | (have j0 := eq593 x y X0
       grind)
    | exact resolve eq593 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1205 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq593 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq593
    | (have j0 := eq593 x X0 y
       grind)
    | exact resolve eq593 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1206 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq593
    | (have j0 := eq593 (σ x) X0 (σ y)
       grind)
    | exact resolve eq593 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1212 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq593 X0 X1 x
       grind)
    | exact superpose eq593 eq14
    | exact resolve eq14 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1286 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1212 (σ X0) X1
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq1212
    | exact resolve eq1212 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1288 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1212 X0 (M.op X0 X1)
       have i₂ := eq593 X0 X0 X1
       grind)
    | exact superpose eq593 eq1212
    | exact resolve eq1212 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1293 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1 X1 X0
       have i₂ := eq1212 (M.op X0 X1) X0
       grind)
    | exact superpose eq1212 eq55
    | exact resolve eq55 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1300 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X1
       have i₂ := eq1212 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq1212 eq14
    | exact resolve eq14 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1319 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1293 X0 X1
       have i₂ := eq593 X0 X1 X1
       grind)
    | exact superpose eq593 eq1293
    | exact resolve eq1293 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293
  have eq1425 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq1205 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1205
    | (have j0 := eq1205 y
       grind)
    | exact resolve eq1205 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205
  have eq1471 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1425
       have i₂ := eq1189 X0
       grind)
    | exact superpose eq1189 eq1425
    | exact resolve eq1425 eq1189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1640 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq26 eq1206
    | (have j0 := eq1206 (σ y)
       grind)
    | exact resolve eq1206 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206
  have eq1975 : (M.op x x) = (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op x x)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1288 (M.op x x) y
       have i₂ := eq1425
       grind)
    | exact superpose eq1425 eq1288
    | exact resolve eq1288 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1979 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) x) := by
    first
    | exact superpose eq239 eq1288
    | exact resolve eq1288 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1985 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq248 eq1288
    | exact resolve eq1288 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2023 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq1985
       have i₂ := eq1212 sF4 (M.op sF4 sF4)
       grind)
    | exact superpose eq1212 eq1985
    | exact resolve eq1985 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1985
  have eq2029 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1979
       have i₂ := eq1212 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq1212 eq1979
    | exact resolve eq1979 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1979
  have eq2033 : (M.op x x) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1975
       have i₂ := eq1212 x (M.op x x)
       grind)
    | exact superpose eq1212 eq1975
    | exact resolve eq1975 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212 eq1975
  have eq2071 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq2023 eq248
    | exact resolve eq248 eq2023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq2166 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq2029 eq239
    | exact resolve eq239 eq2029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq2180 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2029 eq593
    | exact resolve eq593 eq2029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2193 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | (have i₁ := eq2180 x
       have i₂ := eq593 sF0 x x
       grind)
    | exact superpose eq593 eq2180
    | exact resolve eq2180 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2180
  have eq2200 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq2029 eq2193
    | exact resolve eq2193 eq2029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2193
  have eq2384 : (M.op x x) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq2029 eq2033
    | exact resolve eq2033 eq2029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2033
  have eq3049 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1319 (M.op X0 X1) X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq1319
    | exact resolve eq1319 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3057 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1319 (M.op (M.op X0 X0) X0) (M.op X0 X1)
       have i₂ := eq1288 X0 X1
       grind)
    | exact superpose eq1288 eq1319
    | exact resolve eq1319 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288
  have eq3145 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3057 X0 X1
       have i₂ := eq1300 X0 X0
       grind)
    | exact superpose eq1300 eq3057
    | exact resolve eq3057 eq1300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300 eq3057
  have eq3151 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3145 X0 X1
       have i₂ := eq593 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq593 eq3145
    | exact resolve eq3145 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3145
  have eq3152 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3151 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq3151
    | exact resolve eq3151 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3151
  have eq3646 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq3152 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3152
    | (have j0 := eq3152 x y
       grind)
    | exact resolve eq3152 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3652 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq3152
    | (have j0 := eq3152 (σ x) (σ y)
       grind)
    | exact resolve eq3152 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3796 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op (M.op x y) x) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq3646 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 (M.op x y) x
       have r₂ := eq3646
       grind)
    | exact resolve eq12 eq3646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3646
  have eq3813 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (k (M.op x y) x) := by grind
  clear eq3796
  have eq3963 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq3652 eq12
    | (have j0 := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq3652
       grind)
    | exact resolve eq12 eq3652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3652
  have eq3980 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq3963
  have eq4360 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) y) := by
    intro X1
    first
    | exact superpose eq1471 eq243
    | (have j0 := eq243 y X1
       grind)
    | exact resolve eq243 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq4361 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) y) := by
    intro X1
    first
    | exact superpose eq2029 eq4360
    | exact resolve eq4360 eq2029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4360
  have eq4510 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq4361 eq3049
    | exact resolve eq3049 eq4361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4361
  have eq4573 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3152 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq3049 X0 X1
       grind)
    | exact superpose eq3049 eq3152
    | exact resolve eq3152 eq3049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3152
  have eq4574 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4573 X0 X1
       have i₂ := eq593 (M.op X0 X1) X1 X1
       grind)
    | exact superpose eq593 eq4573
    | exact resolve eq4573 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4573
  have eq4614 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op x (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq2166 eq4510
    | exact resolve eq4510 eq2166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4510
  have eq4632 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4574 X0 X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq4574
    | exact resolve eq4574 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4574
  have eq4656 : ∀ X0 : G, (M.op x x) = (M.op x (M.op (M.op (M.op x y) x) X0)) := by
    intro X0
    first
    | exact superpose eq2384 eq4614
    | exact resolve eq4614 eq2384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2384 eq4614
  have eq12839 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq972 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq972
    | (have j0 := eq972 x
       grind)
    | exact resolve eq972 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq12881 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12839
       have i₂ := eq101
       grind)
    | exact superpose eq101 eq12839
    | exact resolve eq12839 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12839
  have eq12903 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | exact superpose eq26 eq12881
    | exact resolve eq12881 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12881
  have eq12915 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | exact superpose eq26 eq12903
    | exact resolve eq12903 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12903
  have eq12924 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12915
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq12915
    | exact resolve eq12915 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12915
  have eq12932 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12924
    | exact resolve eq12924 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12924
  have eq13631 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1471 eq572
    | (have j0 := eq572 y X1 X2
       grind)
    | exact resolve eq572 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq1471
  have eq13632 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) x) X1)) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq2029 eq13631
    | exact resolve eq13631 eq2029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13631
  have eq13633 : ∀ X2 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x x) X2)) y) := by
    intro X2
    first
    | exact superpose eq4656 eq13632
    | exact resolve eq13632 eq4656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4656 eq13632
  have eq13727 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x y) (M.op x X0))) y) := by
    intro X0
    first
    | (have i₁ := eq13633 y
       have i₂ := eq1189 X0
       grind)
    | exact superpose eq1189 eq13633
    | exact resolve eq13633 eq1189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189 eq13633
  have eq13781 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) y) := by
    first
    | (have i₁ := eq13727 x
       have i₂ := eq593 sF0 x (M.op x x)
       grind)
    | exact superpose eq593 eq13727
    | exact resolve eq13727 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593 eq13727
  have eq13803 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) y) := by
    first
    | (have i₁ := eq13781
       have i₂ := eq1319 sF0 x
       grind)
    | exact superpose eq1319 eq13781
    | exact resolve eq13781 eq1319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319 eq13781
  have eq13819 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) x) y) := by
    first
    | exact superpose eq2200 eq13803
    | exact resolve eq13803 eq2200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13803
  have eq35696 : x = (M.op (M.op x x) y) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq3813 eq2166
    | exact resolve eq2166 eq3813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2166 eq3813
  have eq35816 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq35696
       have i₂ := eq1425
       grind)
    | exact superpose eq1425 eq35696
    | exact resolve eq35696 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425 eq35696
  have eq35830 : x = (k (M.op x y) x) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq2029 eq35816
    | exact resolve eq35816 eq2029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2029 eq35816
  have eq38540 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq3980 eq2071
    | exact resolve eq2071 eq3980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3980
  have eq38648 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1640 eq38540
    | exact resolve eq38540 eq1640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1640 eq38540
  have eq38663 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq2023 eq38648
    | exact resolve eq38648 eq2023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2023 eq38648
  have eq63414 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq119 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63415 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq63414
    | exact resolve eq63414 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63414
  have eq63426 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq63415
       have r₂ := eq27
       grind)
    | exact resolve eq63415 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63415
  have eq63430 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq63426
    | exact resolve eq63426 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63426
  have eq63434 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq63430
    | exact resolve eq63430 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63430
  have eq63437 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq63434 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq63434
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq63434
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq63434
       grind)
    | exact resolve eq13 eq63434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63434
  have eq63474 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq63437
       have r₂ := eq26
       grind)
    | exact resolve eq63437 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63437
  have eq64539 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq63474 eq119
    | exact resolve eq119 eq63474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63474
  have eq64547 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq64539
  have eq64549 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq64547
       have r₂ := eq27
       grind)
    | exact resolve eq64547 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64547
  have eq64828 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq64549 eq79
    | (have r₁ := eq79
       have r₂ := eq64549
       grind)
    | exact resolve eq79 eq64549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq64549
  have eq64974 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq64828
  have eq80270 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq64974 eq4632
    | exact resolve eq4632 eq64974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64974
  have eq80283 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq2071 eq80270
    | exact resolve eq80270 eq2071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80270
  have eq80300 : (τ (σ x)) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq80283 eq115
    | exact resolve eq115 eq80283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq80301 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq80283 eq119
    | exact resolve eq119 eq80283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq80283
  have eq80312 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq80301
  have eq80322 : x = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq28 eq80300
    | exact resolve eq80300 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80300
  have eq80329 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have r₁ := eq80322
       have r₂ := eq78
       grind)
    | exact resolve eq80322 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq80322
  have eq80614 : y = (M.op (M.op (M.op x y) x) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq3049 y x
       have i₂ := eq80329
       grind)
    | exact superpose eq80329 eq3049
    | exact resolve eq3049 eq80329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3049 eq80329
  have eq80633 : y = (M.op (M.op (M.op x y) x) x) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq2200 eq80614
    | exact resolve eq80614 eq2200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2200 eq80614
  have eq81680 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq80633 eq13819
    | exact resolve eq13819 eq80633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13819 eq80633
  have eq86142 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x x)) X0) X0) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq1286 y X0
       have i₂ := eq81680
       grind)
    | exact superpose eq81680 eq1286
    | exact resolve eq1286 eq81680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81680
  have eq86254 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq86142 x
       have i₂ := eq1286 x x
       grind)
    | exact superpose eq1286 eq86142
    | exact resolve eq86142 eq1286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286 eq86142
  have eq86296 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq86254
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq86254
    | exact resolve eq86254 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86254
  have eq86309 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq86296
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq86296
    | exact resolve eq86296 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86296
  have eq86310 : x = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq86309
  have eq86319 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq86310
       grind)
    | exact superpose eq86310 eq101
    | exact resolve eq101 eq86310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86310
  have eq86341 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq86319
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq86319
    | exact resolve eq86319 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86319
  have eq86350 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12932 eq86341
    | exact resolve eq86341 eq12932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12932
  have eq134655 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq80312
       grind)
    | exact superpose eq80312 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq80312
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq80312
       grind)
    | exact resolve eq13 eq80312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80312
  have eq134697 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq134655
       have r₂ := eq18
       grind)
    | exact resolve eq134655 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134655
  have eq135612 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq134697
       grind)
    | exact superpose eq134697 eq101
    | exact resolve eq101 eq134697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq134697
  have eq135796 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq135612
    | exact resolve eq135612 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135612
  have eq146791 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq135796 eq86341
    | exact resolve eq86341 eq135796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86341 eq135796
  have eq146893 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq146791
  have eq146956 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq146893
       grind)
    | exact superpose eq146893 eq73
    | exact resolve eq73 eq146893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146893
  have eq147219 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq146956
    | exact resolve eq146956 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146956
  have eq284308 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq86350 eq4632
    | exact resolve eq4632 eq86350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4632 eq86350
  have eq284325 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2071 eq284308
    | exact resolve eq284308 eq2071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2071 eq284308
  have eq284326 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq284325
  have eq284410 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq284326 eq147219
    | exact resolve eq147219 eq284326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq284611 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq284410
  have eq284695 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq284611
       have r₂ := eq27
       grind)
    | exact resolve eq284611 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284611
  have eq285585 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq284695 eq38663
    | exact resolve eq38663 eq284695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38663 eq284695
  have eq285865 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq285585
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq285585
    | exact resolve eq285585 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285585
  have eq285866 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq285865
  have eq288244 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq285866 eq147219
    | exact resolve eq147219 eq285866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147219 eq285866
  have eq288452 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq288244
  have eq289396 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq288452 eq29
    | exact resolve eq29 eq288452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289633 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq28 eq289396
    | exact resolve eq289396 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289396
  have eq289667 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq289633 eq28
    | exact resolve eq28 eq289633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289633
  have eq290110 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq289667
    | exact resolve eq289667 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq289667
  have eq291109 : x = (k x x) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq290110 eq35830
    | exact resolve eq35830 eq290110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35830 eq290110
  have eq291241 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq291109
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq291109
    | exact resolve eq291109 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq291109
  have eq291242 : x = (M.op x x) ∨ x = y := by grind
  clear eq291241
  have eq294276 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq291242
       grind)
    | exact superpose eq291242 eq73
    | exact resolve eq73 eq291242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq291242
  have eq294635 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq294276
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq294276
    | exact resolve eq294276 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294276
  have eq301171 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq294635 eq284326
    | exact resolve eq284326 eq294635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284326 eq294635
  have eq301348 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq301171
  have eq316719 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq301348 eq27
    | exact resolve eq27 eq301348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301348
  have eq317172 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq316719
       have r₂ := eq288452
       grind)
    | exact resolve eq316719 eq288452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288452 eq316719
  have eq317252 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq317172 eq29
    | exact resolve eq29 eq317172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq317172
  have eq317498 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq317252
    | exact resolve eq317252 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq317252
  have eq317499 : x = y := by grind
  clear eq317498
  have eq317536 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq317499
       grind)
    | exact superpose eq317499 eq18
    | exact resolve eq18 eq317499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq317537 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq317499
       grind)
    | exact superpose eq317499 eq24
    | exact resolve eq24 eq317499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq317499
  have eq318102 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq317537
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq317537
    | exact resolve eq317537 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq317537
  have eq319392 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq318102 eq26
    | exact resolve eq26 eq318102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq318102
  have eq320131 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq319392 eq72
    | exact resolve eq72 eq319392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq319392
  have eq320465 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq320131
       have i₂ := eq317536
       grind)
    | exact superpose eq317536 eq320131
    | exact resolve eq320131 eq317536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317536 eq320131
  have eq320569 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq320465 eq15
    | exact resolve eq15 eq320465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320465
  have eq321044 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq320569
    | exact resolve eq320569 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq320569
  have eq321185 : False := by grind
  exact eq321185

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_pxy_x_pxy_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq54 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
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
  have eq63 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
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
  have eq66 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k x y) := by
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
  have eq70 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq85
    | (have j0 := eq85 (σ X0) (σ X1)
       grind)
    | exact resolve eq85 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq85 x y
       grind)
    | exact superpose eq85 eq44
    | (have j1 := eq85 x y
       grind)
    | exact resolve eq44 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq123 : (τ (σ (M.op x y))) = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq117 eq59
    | exact resolve eq59 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq117 eq85
    | (have j0 := eq85 (σ x) (σ y)
       grind)
    | exact resolve eq85 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq124
    | exact resolve eq124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq126 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq123
    | exact resolve eq123 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq128 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq125
       have r₂ := eq27
       grind)
    | exact resolve eq125 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq130 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq128
    | exact resolve eq128 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq144 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq130 eq66
    | exact resolve eq66 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq145 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq130 eq27
    | exact resolve eq27 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
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
  clear eq50
  have eq232 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq294 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq34
  have eq362 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq130 eq70
    | (have r₁ := eq70
       have r₂ := eq130
       grind)
    | exact resolve eq70 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq130
  have eq363 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq362
  have eq366 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq363 eq117
    | exact resolve eq117 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : (τ (σ x)) = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq363 eq59
    | exact resolve eq59 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq363
  have eq369 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq366
  have eq372 : x = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq367
    | exact resolve eq367 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq377 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq369 eq29
    | exact resolve eq29 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq385 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq369 eq117
    | exact resolve eq117 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq386 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq369 eq144
    | (have r₁ := eq144
       have r₂ := eq369
       grind)
    | exact resolve eq144 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq369
  have eq416 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq386
  have eq417 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq416
  have eq418 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq385
  have eq426 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq377
    | exact resolve eq377 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq461 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq97 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq467 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq426 eq28
    | exact resolve eq28 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq503 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq467
    | exact resolve eq467 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq467
  have eq504 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq503 eq20
    | exact resolve eq20 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509 : y ≠ y ∨ x = y ∨ x = (k x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq503 eq69
    | (have r₁ := eq69
       have r₂ := eq503
       grind)
    | exact resolve eq69 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq503
  have eq516 : y ≠ y ∨ x = y ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq509
  have eq517 : x = y ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq516
  have eq523 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq504
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq504
    | exact resolve eq504 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq566 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq126
       have i₂ := eq372
       grind)
    | exact superpose eq372 eq126
    | exact resolve eq126 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq372
  have eq569 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq566
  have eq590 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq569 eq145
    | exact resolve eq145 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq569
  have eq620 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq590
  have eq694 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) X3) := by
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
  have eq715 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
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
  clear eq52
  have eq755 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq418 eq417
    | exact resolve eq417 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417 eq418
  have eq758 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq755
  have eq836 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq758 eq620
    | (have r₁ := eq620
       have r₂ := eq758
       grind)
    | exact resolve eq620 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620 eq758
  have eq837 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq836
  have eq838 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq837
  have eq857 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq838 eq20
    | exact resolve eq20 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq858 : (σ (k x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq838 eq45
    | exact resolve eq45 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq867 : x = (M.op (M.op y y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq838 eq222
    | exact resolve eq222 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq868 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq838
  have eq874 : (k (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq858
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq858
    | exact resolve eq858 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq875 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq857
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq857
    | exact resolve eq857 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq857
  have eq879 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq875 eq26
    | exact resolve eq26 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq925 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq523 eq232
    | exact resolve eq232 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq937 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq925
       have r₂ := eq868
       grind)
    | exact resolve eq925 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq977 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq879 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq879
       grind)
    | exact resolve eq13 eq879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq1165 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq294 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq294
    | (have j0 := eq294 X0 x
       grind)
    | exact resolve eq294 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq1266 : ∀ X0 : G, (M.op x (M.op (M.op y y) X0)) = (M.op (M.op (M.op y y) (M.op y y)) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq715 (M.op y y) y X0
       have i₂ := eq867
       grind)
    | exact superpose eq867 eq715
    | exact resolve eq715 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1283 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x x) y) := by
    intro X0
    first
    | (have i₁ := eq715 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq715
    | (have j0 := eq715 x y X0
       grind)
    | exact resolve eq715 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1285 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq715
    | (have j0 := eq715 (σ x) (σ y) X0
       grind)
    | exact resolve eq715 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1321 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq715 X0 X1 x
       grind)
    | exact superpose eq715 eq14
    | exact resolve eq14 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1378 : ∀ X0 : G, y = (M.op x (M.op (M.op y y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1266 X0
       have i₂ := eq14 y y y
       grind)
    | exact superpose eq14 eq1266
    | exact resolve eq1266 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266
  have eq2092 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq517
       have r₂ := eq868
       grind)
    | exact resolve eq517 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq2096 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq2092
       grind)
    | exact superpose eq2092 eq44
    | exact resolve eq44 eq2092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2092
  have eq2102 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2096
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2096
    | exact resolve eq2096 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2096
  have eq2118 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2102 eq874
    | exact resolve eq874 eq2102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq2121 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2102 eq85
    | (have j0 := eq85 (σ x) (σ y)
       grind)
    | exact resolve eq85 eq2102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2102
  have eq2122 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq2118
  have eq2127 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2121
    | exact resolve eq2121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2121
  have eq2131 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2127
    | exact resolve eq2127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2127
  have eq2140 : (τ (σ x)) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2122 eq63
    | exact resolve eq63 eq2122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2122
  have eq2142 : x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq2140
    | exact resolve eq2140 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2140
  have eq2210 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2131 eq27
    | exact resolve eq27 eq2131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2131
  have eq2228 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2210
       have r₂ := eq875
       grind)
    | exact resolve eq2210 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875 eq2210
  have eq2236 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2228 eq232
    | exact resolve eq232 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq2245 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2228 eq937
    | exact resolve eq937 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq2246 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq2245
  have eq2590 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq977
       have r₂ := eq2228
       grind)
    | exact resolve eq977 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq2678 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2590 eq63
    | exact resolve eq63 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq2590
  have eq2688 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2678 eq2142
    | exact resolve eq2142 eq2678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2142 eq2678
  have eq2694 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq2688
  have eq14203 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) X3) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq694 X0 X1 x X3 X4
       have i₂ := eq715 X0 X1 x
       grind)
    | exact superpose eq715 eq694
    | exact resolve eq694 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq14329 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X2)) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14203 X1 X1 (M.op (M.op X1 X1) X2) x
       have i₂ := eq14 (M.op X1 X1) X1 X2
       grind)
    | exact superpose eq14 eq14203
    | exact resolve eq14203 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14203
  have eq14408 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14329 X0 X1 x
       have i₂ := eq715 (M.op X0 X0) X0 x
       grind)
    | exact superpose eq715 eq14329
    | exact resolve eq14329 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14329
  have eq14467 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14408 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq14408
    | exact resolve eq14408 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14408
  have eq16636 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1378 y
       have i₂ := eq867
       grind)
    | exact superpose eq867 eq1378
    | exact resolve eq1378 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867 eq1378
  have eq16678 : y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq16636
  have eq26271 : (k x x) = (τ (k (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2694 eq1165
    | exact resolve eq1165 eq2694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165 eq2694
  have eq27189 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2246 eq1321
    | exact resolve eq1321 eq2246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321 eq2246
  have eq29558 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2236 eq1285
    | exact resolve eq1285 eq2236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285 eq2236
  have eq29674 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27189 eq29558
    | exact resolve eq29558 eq27189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27189 eq29558
  have eq29735 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq29674
  have eq30008 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29735 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq29735
       grind)
    | exact resolve eq13 eq29735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29735
  have eq30025 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq30008
       have r₂ := eq2228
       grind)
    | exact resolve eq30008 eq2228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2228 eq30008
  have eq30338 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30025 eq26271
    | exact resolve eq26271 eq30025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26271 eq30025
  have eq30353 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq30338
  have eq30359 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq30353
    | exact resolve eq30353 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq30353
  have eq30463 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq85 x x
       have i₂ := eq30359
       grind)
    | exact superpose eq30359 eq85
    | (have j0 := eq85 x x
       grind)
    | exact resolve eq85 eq30359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30359
  have eq30474 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq30463
  have eq30651 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16678
       have i₂ := eq30474
       grind)
    | exact superpose eq30474 eq16678
    | exact resolve eq16678 eq30474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16678 eq30474
  have eq30724 : x = y ∨ x = (M.op x y) := by grind
  clear eq30651
  have eq30730 : x = (M.op x y) := by
    first
    | (have r₁ := eq30724
       have r₂ := eq868
       grind)
    | exact resolve eq30724 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868 eq30724
  have eq30735 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq30730 eq20
    | exact resolve eq20 eq30730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq30739 : x ≠ x ∨ x = (k x y) := by
    first
    | exact superpose eq30730 eq65
    | (have r₁ := eq65
       have r₂ := eq30730
       grind)
    | exact resolve eq65 eq30730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq30744 : x = (M.op (M.op x x) y) := by
    first
    | exact superpose eq30730 eq222
    | exact resolve eq222 eq30730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq30778 : x = (k x y) := by grind
  clear eq30739
  have eq30791 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq30735
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30735
    | exact resolve eq30735 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30735
  have eq30792 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq30791 eq26
    | exact resolve eq26 eq30791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq31001 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq30778
       grind)
    | exact superpose eq30778 eq44
    | exact resolve eq44 eq30778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq30778
  have eq31022 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq30791 eq31001
    | exact resolve eq31001 eq30791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31001
  have eq31033 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq31022
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31022
    | exact resolve eq31022 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31022
  have eq31043 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq30791 eq31033
    | exact resolve eq31033 eq30791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31033
  have eq31127 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq31043 eq85
    | (have j0 := eq85 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq85 eq31043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq31043
  have eq31137 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq30792 eq31127
    | exact resolve eq31127 eq30792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31127
  have eq31141 : (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq31137
       have r₂ := eq27
       grind)
    | exact resolve eq31137 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31137
  have eq31144 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30792 eq31141
    | exact resolve eq31141 eq30792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31141
  have eq31425 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1283 X0
       have i₂ := eq30744
       grind)
    | exact superpose eq30744 eq1283
    | exact resolve eq1283 eq30744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283 eq30744
  have eq31466 : ∀ X0 : G, x = (M.op x (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq30730 eq31425
    | exact resolve eq31425 eq30730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30730 eq31425
  have eq31470 : x = (M.op x x) := by
    first
    | (have i₁ := eq31466 (M.op x x)
       have i₂ := eq31466 x
       grind)
    | exact superpose eq31466 eq31466
    | exact resolve eq31466 eq31466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31466
  have eq31623 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq31470
       grind)
    | exact superpose eq31470 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq31470
       grind)
    | exact resolve eq13 eq31470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31470
  have eq31635 : x = (k x x) := by grind
  clear eq31623
  have eq31732 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq461 x x
       have i₂ := eq31635
       grind)
    | exact superpose eq31635 eq461
    | (have j0 := eq461 x x
       grind)
    | exact resolve eq461 eq31635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461 eq31635
  have eq31739 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq31732
  have eq31748 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq31739
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31739
    | exact resolve eq31739 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq31739
  have eq31758 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq30791 eq31748
    | exact resolve eq31748 eq30791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31748
  have eq32182 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ x)) X0)) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op (M.op sF2 sF2) x)
       have i₂ := eq14467 sF2 x
       grind)
    | exact superpose eq14467 eq54
    | exact resolve eq54 eq14467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq14467
  have eq32259 : (σ x) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq32182 x
       have i₂ := eq715 (M.op sF2 sF2) sF4 x
       grind)
    | exact superpose eq715 eq32182
    | exact resolve eq32182 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32182
  have eq32358 : (σ x) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (σ y)) := by
    first
    | exact superpose eq31144 eq32259
    | exact resolve eq32259 eq31144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31144 eq32259
  have eq32445 : (σ x) = (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq32358
       have i₂ := eq715 sF2 sF2 sF2
       grind)
    | exact superpose eq715 eq32358
    | exact resolve eq32358 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715 eq32358
  have eq32515 : (σ (M.op x y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq30791 eq32445
    | exact resolve eq32445 eq30791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30791 eq32445
  have eq32571 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq31758 eq32515
    | exact resolve eq32515 eq31758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32515
  have eq32610 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq31758 eq32571
    | exact resolve eq32571 eq31758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31758 eq32571
  have eq32640 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30792 eq32610
    | exact resolve eq32610 eq30792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30792 eq32610
  have eq32665 : False := by grind
  exact eq32665

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then X else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_x_x_pxy_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
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
  have eq175 : x ≠ (M.op x y) ∨ x = (k x y) := by
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
  have eq176 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : y ≠ (M.op x y) ∨ x = (k x y) := by
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
  have eq178 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq531 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq538 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq530 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq530
    | (have j0 := eq530 y
       grind)
    | exact resolve eq530 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq531
    | (have j0 := eq531 (σ y)
       grind)
    | exact resolve eq531 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq709 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq735 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq762 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq709
       grind)
    | exact superpose eq709 eq41
    | exact resolve eq41 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq765 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq762
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq762
    | exact resolve eq762 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq767 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq765
    | exact resolve eq765 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq777 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq767 eq710
    | exact resolve eq710 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq785 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq777
       have r₂ := eq27
       grind)
    | exact resolve eq777 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq791 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq785 eq178
    | (have r₁ := eq178
       have r₂ := eq785
       grind)
    | exact resolve eq178 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq785
  have eq796 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq791
  have eq797 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq796
       have r₂ := eq176
       grind)
    | exact resolve eq796 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq796
  have eq805 : (τ (σ x)) = (k (τ (σ x)) y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq797 eq153
    | exact resolve eq153 eq797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq797
  have eq810 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq805
    | exact resolve eq805 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq813 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq810
       have r₂ := eq177
       grind)
    | exact resolve eq810 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq810
  have eq816 : x = (k x y) := by
    first
    | (have r₁ := eq813
       have r₂ := eq175
       grind)
    | exact resolve eq813 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq813
  have eq820 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq709
       have i₂ := eq816
       grind)
    | exact superpose eq816 eq709
    | exact resolve eq709 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq822 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq816
       grind)
    | exact superpose eq816 eq41
    | exact resolve eq41 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq816
  have eq823 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq820
  have eq825 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq822
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq822
    | exact resolve eq822 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq831 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq825 eq710
    | exact resolve eq710 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710 eq825
  have eq835 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq831
  have eq841 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq823
       grind)
    | exact superpose eq823 eq18
    | exact resolve eq18 eq823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq842 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq823
       grind)
    | exact superpose eq823 eq24
    | exact resolve eq24 eq823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq847 : x = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq538
       have i₂ := eq823
       grind)
    | exact superpose eq823 eq538
    | exact resolve eq538 eq823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq853 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq842
    | exact resolve eq842 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq854 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq835 eq27
    | exact resolve eq27 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq858 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) X0) (σ y)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq835 eq534
    | exact resolve eq534 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq859 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq835 eq547
    | exact resolve eq547 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq860 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq885 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq853 eq854
    | (have r₁ := eq854
       have r₂ := eq853
       grind)
    | exact resolve eq854 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853 eq854
  have eq886 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq885
  have eq894 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq886 eq547
    | exact resolve eq547 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547 eq886
  have eq935 : x = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq847 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq937 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X0)) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq847 eq16
    | exact resolve eq16 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq940 : x = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq935
  have eq946 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (M.op (M.op (σ y) (σ y)) X0) (σ x)) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq859 eq16
    | exact resolve eq16 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq966 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) X0) (σ x)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq894 eq16
    | exact resolve eq16 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1370 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq847 eq937
    | exact resolve eq937 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847 eq937
  have eq1380 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq1370
  have eq1559 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq859 eq946
    | exact resolve eq946 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq1571 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1559
  have eq1702 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1571 eq858
    | exact resolve eq858 eq1571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq1712 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1702
  have eq1716 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1712 eq946
    | exact resolve eq946 eq1712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946 eq1712
  have eq1726 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1716
  have eq1900 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq894 eq966
    | exact resolve eq966 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966
  have eq1917 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1900
  have eq1921 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq894 eq1917
    | exact resolve eq1917 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894 eq1917
  have eq1951 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1921 eq28
    | (have j0 := eq28 (σ x) (σ x)
       grind)
    | (have r₁ := eq28 (σ x) (σ x)
       have r₂ := eq1921
       grind)
    | exact resolve eq28 eq1921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1921
  have eq1956 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1951
  have eq1982 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1956 eq142
    | exact resolve eq142 eq1956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq1956
  have eq1990 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq1982
    | exact resolve eq1982 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1982
  have eq1997 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq735 x x
       have i₂ := eq1990
       grind)
    | exact superpose eq1990 eq735
    | (have j0 := eq735 x x
       grind)
    | (have r₁ := eq735 x x
       have r₂ := eq1990
       grind)
    | exact resolve eq735 eq1990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1990
  have eq1998 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq1997
  have eq1999 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq1998
  have eq2006 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1380
       have i₂ := eq1999
       grind)
    | exact superpose eq1999 eq1380
    | exact resolve eq1380 eq1999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1380 eq1999
  have eq2021 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq2006
  have eq2025 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq841 eq2021
    | exact resolve eq2021 eq841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841 eq2021
  have eq2041 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2025 eq940
    | exact resolve eq940 eq2025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq2050 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2025 eq28
    | (have j0 := eq28 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq28 (M.op x y) (M.op x y)
       have r₂ := eq2025
       grind)
    | exact resolve eq28 eq2025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2025
  have eq2055 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq2050
  have eq2062 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq2041
  have eq2068 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2055 eq2062
    | exact resolve eq2062 eq2055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2055 eq2062
  have eq2069 : x = (M.op x y) := by grind
  clear eq2068
  have eq2076 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2069
       grind)
    | exact superpose eq2069 eq18
    | exact resolve eq18 eq2069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2077 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq2069
       grind)
    | exact superpose eq2069 eq22
    | exact resolve eq22 eq2069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq2079 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq2069
       grind)
    | exact superpose eq2069 eq40
    | exact resolve eq40 eq2069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq2081 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) y) := by
    intro X0
    first
    | (have i₁ := eq530 X0
       have i₂ := eq2069
       grind)
    | exact superpose eq2069 eq530
    | exact resolve eq530 eq2069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq2086 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2077 eq20
    | exact resolve eq20 eq2077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077
  have eq2624 : (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq2076 eq2081
    | exact resolve eq2081 eq2076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2076 eq2081
  have eq2652 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) X0)) y) := by
    intro X0
    first
    | exact superpose eq2624 eq16
    | exact resolve eq16 eq2624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3095 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq2624 eq2652
    | exact resolve eq2652 eq2624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2624 eq2652
  have eq3116 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq538 eq3095
    | exact resolve eq3095 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538 eq3095
  have eq3119 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq3116
       have i₂ := eq2069
       grind)
    | exact superpose eq2069 eq3116
    | exact resolve eq3116 eq2069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2069 eq3116
  have eq3144 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3119 eq28
    | (have j0 := eq28 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq28 (M.op x y) (M.op x y)
       have r₂ := eq3119
       grind)
    | exact resolve eq28 eq3119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3119
  have eq3151 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq3144
  have eq3163 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq3151 eq2079
    | exact resolve eq2079 eq3151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2079 eq3151
  have eq3176 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq3163
    | exact resolve eq3163 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3163
  have eq3180 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq2086 eq3176
    | exact resolve eq3176 eq2086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3176
  have eq3194 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3180 eq735
    | (have j0 := eq735 (σ x) (σ x)
       grind)
    | (have r₁ := eq735 (σ x) (σ x)
       have r₂ := eq3180
       grind)
    | exact resolve eq735 eq3180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735 eq3180
  have eq3195 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3194
  have eq3196 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3195
  have eq3216 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3196 eq1571
    | exact resolve eq1571 eq3196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1571
  have eq3218 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3196 eq1726
    | exact resolve eq1726 eq3196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726
  have eq3246 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3196 eq3218
    | exact resolve eq3218 eq3196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3196 eq3218
  have eq3247 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3216
    | exact resolve eq3216 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3216
  have eq3249 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq835 eq3247
    | exact resolve eq3247 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835 eq3247
  have eq3250 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3246 eq3249
    | exact resolve eq3249 eq3246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3246 eq3249
  have eq3251 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3250
       have r₂ := eq860
       grind)
    | exact resolve eq3250 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860 eq3250
  have eq3254 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq3251 eq27
    | exact resolve eq27 eq3251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3251
  have eq3262 : False := by grind
  exact eq3262
