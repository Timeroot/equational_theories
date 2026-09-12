import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_pxx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  have eq176 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
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
  have eq177 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq16 X0 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 (M.op X1 x)
       have i₂ := eq16 X0 X1 x
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
  have eq209 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X1
       have i₂ := eq180 X0 X1
       grind)
    | exact superpose eq180 eq177
    | exact resolve eq177 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq210 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X1
       have i₂ := eq180 X0 X1
       grind)
    | exact superpose eq180 eq176
    | exact resolve eq176 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X2
       have i₂ := eq180 X0 X2
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X1 X1
       have i₂ := eq180 X1 X0
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq218 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq213 X0 X1 X2
       have i₂ := eq179 X0 X0 X1
       grind)
    | exact superpose eq179 eq213
    | exact resolve eq213 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq221 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op x (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq210 X0 X1
       have i₂ := eq215 X0 X0
       grind)
    | exact superpose eq215 eq210
    | exact resolve eq210 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq222 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ x) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq209 X0 X1
       have i₂ := eq215 X0 X0
       grind)
    | exact superpose eq215 eq209
    | exact resolve eq209 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq215
  have eq1824 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
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
  have eq1829 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1894 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2016 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1824
       grind)
    | exact superpose eq1824 eq41
    | exact resolve eq41 eq1824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1824
  have eq2017 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2016
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2016
    | exact resolve eq2016 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2016
  have eq2019 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq2017
    | exact resolve eq2017 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2017
  have eq2027 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2019 eq1829
    | exact resolve eq1829 eq2019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1829 eq2019
  have eq2034 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2027
       have r₂ := eq27
       grind)
    | exact resolve eq2027 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2027
  have eq2040 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ x) (M.op X1 (σ y))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2034 eq222
    | exact resolve eq222 eq2034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq2069 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq2040
    | (have j0 := eq2040 X0 (σ x)
       grind)
    | exact resolve eq2040 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040
  have eq2151 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2034 eq2069
    | exact resolve eq2069 eq2034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2069
  have eq2174 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq2151
    | (have j0 := eq2151 X0
       grind)
    | exact resolve eq2151 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2151
  have eq2188 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2034 eq2174
    | exact resolve eq2174 eq2034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2034 eq2174
  have eq2241 : ∀ X0 : G, (σ y) = (k X0 X0) ∨ (σ y) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq28 X0 X0
       have i₂ := eq2188 X0
       grind)
    | exact superpose eq2188 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq2188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq2247 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq179 x (M.op x x) x
       have i₂ := eq2188 (M.op x x)
       grind)
    | exact superpose eq2188 eq179
    | exact resolve eq179 eq2188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq2406 : (σ y) = (k (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2247 eq183
    | exact resolve eq183 eq2247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2410 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2188 eq2406
    | exact resolve eq2406 eq2188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2188 eq2406
  have eq2446 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2410 eq153
    | exact resolve eq153 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq2410
  have eq2447 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq2446
    | exact resolve eq2446 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq2446
  have eq2681 : y = (σ y) ∨ y = (M.op x y) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2447
       have i₂ := eq2241 y
       grind)
    | exact superpose eq2241 eq2447
    | (have j1 := eq2241 y
       grind)
    | exact resolve eq2447 eq2241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2241 eq2447
  have eq2688 : y = (σ y) ∨ y = (M.op x y) := by grind
  clear eq2681
  have eq2722 : (M.op x y) = (M.op x (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2688
       grind)
    | exact superpose eq2688 eq18
    | exact resolve eq18 eq2688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2728 : (M.op x y) ≠ (σ y) ∨ y = (M.op x y) := by grind
  clear eq2688
  have eq2776 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2722 eq2247
    | exact resolve eq2247 eq2722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2247 eq2722
  have eq2783 : (M.op x y) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq2776
  have eq2788 : y = (M.op x y) := by
    first
    | (have r₁ := eq2783
       have r₂ := eq2728
       grind)
    | exact resolve eq2783 eq2728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2728 eq2783
  have eq2793 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2788
       grind)
    | exact superpose eq2788 eq18
    | exact resolve eq18 eq2788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2794 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2788
       grind)
    | exact superpose eq2788 eq24
    | exact resolve eq24 eq2788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2788
  have eq2798 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2794 eq20
    | exact resolve eq20 eq2794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2794
  have eq2859 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2793 eq221
    | exact resolve eq221 eq2793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq2860 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq2793 eq176
    | exact resolve eq176 eq2793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq2865 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq2793 eq2860
    | exact resolve eq2860 eq2793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2860
  have eq2866 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2793 eq2859
    | exact resolve eq2859 eq2793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2793 eq2859
  have eq2882 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq218 x X0 X1
       have i₂ := eq2865
       grind)
    | exact superpose eq2865 eq218
    | exact resolve eq218 eq2865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq2865
  have eq2894 : ∀ X1 : G, (M.op x y) = (M.op X1 (M.op x y)) := by
    intro X1
    first
    | (have i₁ := eq2882 x X1
       have i₂ := eq2866 x
       grind)
    | exact superpose eq2866 eq2882
    | exact resolve eq2882 eq2866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2882
  have eq3036 : (M.op x y) = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq2894 eq183
    | exact resolve eq183 eq2894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq3039 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq3036
       have i₂ := eq2866 sF0
       grind)
    | exact superpose eq2866 eq3036
    | exact resolve eq3036 eq2866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3036
  have eq3519 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3039 eq38
    | exact resolve eq38 eq3039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq3039
  have eq3527 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq3519
    | exact resolve eq3519 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3519
  have eq3529 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq2798 eq3527
    | exact resolve eq3527 eq2798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3527
  have eq3535 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3529 eq1894
    | (have j0 := eq1894 (σ y) (σ y)
       grind)
    | (have r₁ := eq1894 (σ y) (σ y)
       have r₂ := eq3529
       grind)
    | exact resolve eq1894 eq3529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894 eq3529
  have eq3536 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3535
  have eq3537 : (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq3536
       have i₂ := eq2866 sF3
       grind)
    | exact superpose eq2866 eq3536
    | exact resolve eq3536 eq2866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2866 eq3536
  have eq3545 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq3537 eq26
    | exact resolve eq26 eq3537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq3581 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2894 eq3545
    | exact resolve eq3545 eq2894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2894 eq3545
  have eq3595 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq3581 eq27
    | exact resolve eq27 eq3581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3581
  have eq3605 : (M.op x y) ≠ (σ y) := by
    first
    | exact superpose eq2798 eq3595
    | exact resolve eq3595 eq2798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2798 eq3595
  have eq3608 : False := by grind
  exact eq3608

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pxy_pyy_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
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
  have eq44 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  clear eq25 eq36
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X1 (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X1 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X1 (M.op X0 X2))) X1) = (M.op (M.op X0 (M.op X1 (M.op X0 X2))) X1) := by
    intro X0 X1 X2
    grind
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq84
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq92
    | exact resolve eq92 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq240 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 x X0
       have i₂ := eq56 x X1
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 X1
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X1 X1 X2
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1110 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) X1) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq67 x X1 (M.op X0 (M.op X1 (M.op X0 x)))
       have i₂ := eq54 X0 X1 x x
       grind)
    | exact superpose eq54 eq67
    | exact resolve eq67 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq67
  have eq1138 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1110 X0 X1
       have i₂ := eq248 X0 X0
       grind)
    | exact superpose eq248 eq1110
    | exact resolve eq1110 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq1311 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X0
       have i₂ := eq56 X0 (σ X0)
       grind)
    | exact superpose eq56 eq77
    | exact resolve eq77 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1326 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X1 (σ X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq56
    | (have j1 := eq77 X0 X0
       grind)
    | exact resolve eq56 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1344 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1345 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1344 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344
  have eq1355 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1326 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326
  have eq1370 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1311 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311
  have eq1377 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1355 X0 X1
       have i₂ := eq248 X1 X1
       grind)
    | exact superpose eq248 eq1355
    | (have j0 := eq1355 X0 X1
       grind)
    | exact resolve eq1355 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355
  have eq1379 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1370 X0 X1
       have i₂ := eq248 X0 X0
       grind)
    | exact superpose eq248 eq1370
    | (have j0 := eq1370 X0 X1
       grind)
    | exact resolve eq1370 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370
  have eq1395 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1379 X0 X1
       have i₂ := eq248 X0 X0
       grind)
    | exact superpose eq248 eq1379
    | (have j0 := eq1379 X0 X1
       grind)
    | exact resolve eq1379 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq1379
  have eq5618 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X1)
       have i₂ := eq1395 X0 (τ X1)
       grind)
    | exact superpose eq1395 eq35
    | (have j1 := eq1395 X0 (τ X1)
       grind)
    | exact resolve eq35 eq1395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395
  have eq5649 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5618 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq5618
    | (have j0 := eq5618 X0 X1
       grind)
    | exact resolve eq5618 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5618
  have eq5709 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5649 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq5649
    | (have j0 := eq5649 X0 X1
       grind)
    | exact resolve eq5649 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5649
  have eq8250 : ∀ X0 : G, (k (σ x) (σ x)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq44
       have i₂ := eq5709 X0 x
       grind)
    | exact superpose eq5709 eq44
    | (have j1 := eq5709 X0 x
       grind)
    | exact resolve eq44 eq5709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10241 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1345 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq1345
    | (have j0 := eq1345 (τ X0)
       grind)
    | exact resolve eq1345 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1345
  have eq10249 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq10241 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10241
    | (have j0 := eq10241 X0
       grind)
    | exact resolve eq10241 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10241
  have eq10258 : ∀ X0 : G, (σ (τ X0)) = (M.op x (M.op (σ (τ X0)) (M.op x y))) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq10249 X0
       have i₂ := eq52 (σ (τ X0))
       grind)
    | exact superpose eq52 eq10249
    | (have j0 := eq10249 X0
       grind)
    | exact resolve eq10249 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10249
  have eq10263 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op x (M.op X0 (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq10258 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10258
    | (have j0 := eq10258 X0
       grind)
    | exact resolve eq10258 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10258
  have eq10474 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ (k x x)) := by
    intro X0
    first
    | (have i₁ := eq1377 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1377
    | (have j0 := eq1377 x X0
       grind)
    | exact resolve eq1377 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377
  have eq10579 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10474 X0
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq10474
    | exact resolve eq10474 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10474
  have eq11280 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op x (M.op (σ x) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq10579 eq10263
    | (have j0 := eq10263 (σ x)
       grind)
    | exact resolve eq10263 eq10579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10263 eq10579
  have eq11292 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq52 eq11280
    | (have j0 := eq11280 X0
       grind)
    | exact resolve eq11280 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq11280
  have eq11293 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq11292 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11292
  have eq44096 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq93 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44104 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq44096
    | exact resolve eq44096 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44096
  have eq44115 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq44104
       have r₂ := eq28
       grind)
    | exact resolve eq44104 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44104
  have eq44120 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq44115
  have eq44200 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq44120
    | exact resolve eq44120 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44120
  have eq44234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq44200 eq93
    | exact resolve eq93 eq44200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq44200
  have eq44250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq44234
  have eq44253 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq44250
       have r₂ := eq28
       grind)
    | exact resolve eq44250 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44250
  have eq44256 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) (M.op X0 (σ x))) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq44253 eq14
    | exact resolve eq14 eq44253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44344 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq44253 eq44256
    | exact resolve eq44256 eq44253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44256
  have eq44567 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq44344
  have eq44666 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq44567 eq11293
    | exact resolve eq11293 eq44567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11293 eq44567
  have eq44697 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq44666
       have r₂ := eq44253
       grind)
    | exact resolve eq44666 eq44253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44666
  have eq44702 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  have eq44711 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq44697 eq411
    | exact resolve eq411 eq44697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq46380 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq44697
       have i₂ := eq44711 sF2 x
       grind)
    | exact superpose eq44711 eq44697
    | exact resolve eq44697 eq44711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44697
  have eq46462 : ∀ X0 : G, x ≠ (M.op X0 (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    intro X0
    grind
  clear eq44711
  have eq46473 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq46380 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46380
  have eq46564 : x ≠ (σ x) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq44253 eq46462
    | exact resolve eq46462 eq44253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44253 eq46462
  have eq46567 : x ≠ (σ x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq46564
  have eq46611 : (k (σ x) (σ x)) = (σ (σ x)) ∨ x = (σ x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq46473 eq8250
    | (have j0 := eq8250 y
       grind)
    | exact resolve eq8250 eq46473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8250
  have eq46673 : (k (σ x) (σ x)) = (σ (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq46611
       have r₂ := eq46567
       grind)
    | exact resolve eq46611 eq46567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46611
  have eq46803 : (M.op (σ x) (σ x)) = (σ (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq46673 eq44702
    | exact resolve eq44702 eq46673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44702 eq46673
  have eq46836 : (M.op (σ x) (σ x)) = (σ (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq46803
  have eq46950 : (σ x) = (σ (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq46836 eq46473
    | exact resolve eq46473 eq46836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46473 eq46836
  have eq47028 : x = (M.op y y) ∨ (σ x) = (σ (σ x)) ∨ x = (M.op y x) := by grind
  clear eq46950
  have eq47062 : ∀ X0 : G, (M.op X0 X0) = (M.op y x) ∨ (σ x) = (σ (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq56 y X0
       have i₂ := eq47028
       grind)
    | exact superpose eq47028 eq56
    | exact resolve eq56 eq47028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48072 : x = (M.op y x) ∨ (σ x) = (σ (σ x)) ∨ x = (M.op y x) ∨ (σ x) = (σ (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq47028
       have i₂ := eq47062 y
       grind)
    | exact superpose eq47062 eq47028
    | exact resolve eq47028 eq47062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47028 eq47062
  have eq48114 : x = (M.op y x) ∨ (σ x) = (σ (σ x)) := by grind
  clear eq48072
  have eq48204 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op X0 x)) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq48114
       grind)
    | exact superpose eq48114 eq14
    | exact resolve eq14 eq48114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48299 : (M.op y x) = (M.op y y) ∨ (σ x) = (σ (σ x)) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq48204 y
       have i₂ := eq48114
       grind)
    | exact superpose eq48114 eq48204
    | exact resolve eq48204 eq48114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48204
  have eq48533 : (M.op y x) = (M.op y y) ∨ (σ x) = (σ (σ x)) := by grind
  clear eq48299
  have eq48594 : ∀ X0 : G, (M.op X0 X0) = (M.op y x) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq48533
       have i₂ := eq240 y X0
       grind)
    | (have i₁ := eq48533
       have i₂ := eq240 X0 y
       grind)
    | exact superpose eq240 eq48533
    | exact resolve eq48533 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq48533
  have eq48974 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ x) = (σ (σ x)) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq48114
       have i₂ := eq48594 X0
       grind)
    | exact superpose eq48594 eq48114
    | exact resolve eq48114 eq48594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48114 eq48594
  have eq49000 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | (have j0 := eq48974 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48974
  have eq49149 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    grind
  have eq49200 : ∀ X1 : G, x = (k X1 X1) ∨ x = X1 ∨ (σ x) = (σ (σ x)) := by
    intro X1
    first
    | (have i₁ := eq5709 x X1
       have i₂ := eq49000 x
       grind)
    | exact superpose eq49000 eq5709
    | exact resolve eq5709 eq49000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5709
  have eq50551 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq49149 x
       grind)
    | exact superpose eq49149 eq44
    | exact resolve eq44 eq49149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq49149
  have eq54239 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ (σ x)) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq50551
       have i₂ := eq49000 x
       grind)
    | exact superpose eq49000 eq50551
    | exact resolve eq50551 eq49000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49000 eq50551
  have eq54333 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ (σ x)) := by grind
  clear eq54239
  have eq54389 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq54333
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq54333
    | exact resolve eq54333 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq54333
  have eq54450 : x = (σ x) ∨ x = (σ x) ∨ (σ x) = (σ (σ x)) ∨ (σ x) = (σ (σ x)) := by
    first
    | exact superpose eq54389 eq49200
    | (have j0 := eq49200 (σ x)
       grind)
    | exact resolve eq49200 eq54389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49200 eq54389
  have eq54468 : (σ x) = (σ (σ x)) ∨ x = (σ x) := by grind
  clear eq54450
  have eq54504 : (σ x) = (τ (σ x)) ∨ x = (σ x) := by
    first
    | exact superpose eq54468 eq16
    | exact resolve eq16 eq54468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54468
  have eq54585 : x = (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq54504
    | exact resolve eq54504 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq54504
  have eq54586 : x = (σ x) := by grind
  clear eq54585
  have eq54591 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq54586 eq27
    | exact resolve eq27 eq54586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq54681 : x ≠ x ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq54586 eq46567
    | (have r₁ := eq46567
       have r₂ := eq54586
       grind)
    | exact resolve eq46567 eq54586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46567
  have eq54691 : x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq54681
  have eq56771 : ∀ X0 : G, (M.op X0 X0) = (M.op y x) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq56 y X0
       have i₂ := eq54691
       grind)
    | exact superpose eq54691 eq56
    | exact resolve eq56 eq54691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq66295 : x = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq54691
       have i₂ := eq56771 y
       grind)
    | exact superpose eq56771 eq54691
    | exact resolve eq54691 eq56771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54691 eq56771
  have eq66355 : x = (M.op y x) := by grind
  clear eq66295
  have eq66520 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq66355
       grind)
    | exact superpose eq66355 eq14
    | exact resolve eq14 eq66355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67003 : (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq66520 y
       have i₂ := eq66355
       grind)
    | exact superpose eq66355 eq66520
    | exact resolve eq66520 eq66355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66520
  have eq67324 : x = (M.op y y) := by
    first
    | (have i₁ := eq67003
       have i₂ := eq66355
       grind)
    | exact superpose eq66355 eq67003
    | exact resolve eq67003 eq66355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66355 eq67003
  have eq67400 : (M.op x y) = (k x y) := by grind
  have eq67417 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq1138 y x
       have i₂ := eq67324
       grind)
    | exact superpose eq67324 eq1138
    | exact resolve eq1138 eq67324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138 eq67324
  have eq67503 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq67400
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq67400
    | exact resolve eq67400 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq67400
  have eq68270 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq67503
       grind)
    | exact superpose eq67503 eq45
    | exact resolve eq45 eq67503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq67503
  have eq68303 : (σ (M.op x y)) = (k x (σ y)) := by
    first
    | exact superpose eq54586 eq68270
    | exact resolve eq68270 eq54586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54586 eq68270
  have eq68319 : (σ (M.op x y)) = (k x (σ y)) := by
    first
    | exact superpose eq21 eq68303
    | exact resolve eq68303 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq68303
  have eq70964 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq68319
       have i₂ := eq67417 sF3
       grind)
    | exact superpose eq67417 eq68319
    | exact resolve eq68319 eq67417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67417 eq68319
  have eq70965 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54591 eq70964
    | exact resolve eq70964 eq54591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54591 eq70964
  have eq71089 : False := by grind
  exact eq71089

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxx_pyy_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
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
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
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
  have eq55 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
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
  have eq76 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq110 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq110 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq110 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq110 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq125 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq101
       have i₂ := eq112 sF3
       grind)
    | exact superpose eq112 eq101
    | exact resolve eq101 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq126 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq125
       have i₂ := eq112 y
       grind)
    | exact superpose eq112 eq125
    | exact resolve eq125 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq136 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq139 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq136
       have i₂ := eq112 sF1
       grind)
    | exact superpose eq112 eq136
    | exact resolve eq136 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq142 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq139
       have i₂ := eq112 sF0
       grind)
    | exact superpose eq112 eq139
    | exact resolve eq139 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq139
  have eq283 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x X0
       have i₂ := eq55 x X1
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq354 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq142
       have i₂ := eq283 sF0 x
       grind)
    | (have i₁ := eq142
       have i₂ := eq283 X0 sF0
       grind)
    | exact superpose eq283 eq142
    | exact resolve eq142 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op x (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq354 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq354
    | exact resolve eq354 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq354
  have eq915 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq76 X1 X0
       grind)
    | (have i₁ := eq12 (σ X1) (σ X1)
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq12
    | (have j0 := eq12 (σ X0) (σ X0)
       have j1 := eq76 X1 X0
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
  have eq945 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq948 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq915 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq949 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq948 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq952 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq949 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq949
    | (have j0 := eq949 X0 X1
       grind)
    | exact resolve eq949 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq21766 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq952 X0 X1
       have j1 := eq945 X1 X0
       grind)
    | (have r₁ := eq952 X1 X0
       have r₂ := eq945 X0 X1
       grind)
    | (have r₁ := eq952 X1 X1
       have r₂ := eq945 X1 X1
       grind)
    | exact resolve eq952 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945 eq952
  have eq21864 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21766 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq21766
    | exact resolve eq21766 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21941 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq21766 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21766
    | (have j0 := eq21766 y X0
       grind)
    | exact resolve eq21766 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21766
  have eq22288 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21864 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq21864
    | (have j0 := eq21864 X0 X1
       grind)
    | exact resolve eq21864 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq21864
  have eq35243 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq21941 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21941
    | (have j0 := eq21941 x
       grind)
    | exact resolve eq21941 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq21941
  have eq35278 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq35243
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq35243
    | exact resolve eq35243 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35243
  have eq35317 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq35278
    | exact resolve eq35278 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35278
  have eq35715 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22288 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq22288
    | (have j0 := eq22288 X1 X1
       grind)
    | exact resolve eq22288 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22288
  have eq36353 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq35715 x y
       grind)
    | exact superpose eq35715 eq44
    | (have j1 := eq35715 x y
       grind)
    | exact resolve eq44 eq35715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq35715
  have eq36554 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq36353
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq36353
    | exact resolve eq36353 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36353
  have eq36670 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq36554
    | exact resolve eq36554 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36554
  have eq36690 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq36670 eq35317
    | exact resolve eq35317 eq36670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35317 eq36670
  have eq36697 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq36690
       have r₂ := eq27
       grind)
    | exact resolve eq36690 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36690
  have eq36938 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq36697 eq126
    | exact resolve eq126 eq36697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq36697
  have eq37034 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq36938
    | exact resolve eq36938 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq36938
  have eq37035 : y = (M.op y y) := by grind
  clear eq37034
  have eq37044 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq37035
       have i₂ := eq283 y X0
       grind)
    | (have i₁ := eq37035
       have i₂ := eq283 X0 y
       grind)
    | exact superpose eq283 eq37035
    | exact resolve eq37035 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283 eq37035
  have eq37323 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op x x) x x
       have i₂ := eq37044 (M.op x x)
       grind)
    | exact superpose eq37044 eq14
    | exact resolve eq14 eq37044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37374 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq417 sF0
       have i₂ := eq37044 sF0
       grind)
    | exact superpose eq37044 eq417
    | exact resolve eq417 eq37044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq37420 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq142
       have i₂ := eq37044 sF0
       grind)
    | exact superpose eq37044 eq142
    | exact resolve eq142 eq37044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq37492 : y = (σ y) := by
    first
    | (have i₁ := eq37420
       have i₂ := eq37044 sF1
       grind)
    | exact superpose eq37044 eq37420
    | exact resolve eq37420 eq37044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37420
  have eq37526 : y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq37374
       have i₂ := eq37044 sF1
       grind)
    | exact superpose eq37044 eq37374
    | exact resolve eq37374 eq37044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37044 eq37374
  have eq37661 : y = (σ y) := by
    first
    | (have i₁ := eq37492
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37492
    | exact resolve eq37492 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq37492
  have eq37686 : y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq37526
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq37526
    | exact resolve eq37526 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq37526
  have eq37731 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq37686
    | exact resolve eq37686 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq37686
  have eq38001 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq37661 eq26
    | exact resolve eq26 eq37661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq37661
  have eq39121 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq38001
       have i₂ := eq37323 sF2
       grind)
    | exact superpose eq37323 eq38001
    | exact resolve eq38001 eq37323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37323 eq38001
  have eq39122 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq39121 eq27
    | exact resolve eq27 eq39121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq39121
  have eq39135 : False := by grind
  exact eq39135

/-- `Equation335`: `x ◇ y = y ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation335 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law335 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law335.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq881 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X1 X0) (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq908 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq881 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq909 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq908 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq1010 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq909 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq1013 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1010 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq1010 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq1010 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq1010 X0 X1
       have r₂ := eq14 (M.op X1 X0) (M.op X0 X0)
       grind)
    | exact resolve eq1010 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq1065 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq1013 X1 (τ X0)
       grind)
    | exact superpose eq1013 eq20
    | (have j1 := eq1013 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq20 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1068 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1013 (σ X1) (σ X0)
       grind)
    | exact superpose eq1013 eq15
    | (have j1 := eq1013 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq1163 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1065 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1065
    | exact resolve eq1065 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq1215 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1163 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1163
    | (have j0 := eq1163 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq1163 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1410 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1068 x y
       grind)
    | exact superpose eq1068 eq16
    | (have j1 := eq1068 x y
       grind)
    | exact resolve eq16 eq1068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq1444 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1410
       have i₂ := eq1215 x y
       grind)
    | exact superpose eq1215 eq1410
    | (have j1 := eq1215 (σ x) (σ y)
       grind)
    | (have r₁ := eq1410
       have r₂ := eq1215 x y
       grind)
    | (have r₁ := eq1410
       have r₂ := eq1215 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1410
       have r₂ := eq1215 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1410 eq1215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215 eq1410
  have eq1445 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1444
  have eq1449 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1445
       grind)
    | exact superpose eq1445 eq10
    | exact resolve eq10 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445
  have eq1492 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1449
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1449
    | exact resolve eq1449 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449
  have eq1493 : x = y := by grind
  clear eq1492
  have eq1495 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1493
       grind)
    | exact superpose eq1493 eq16
    | exact resolve eq16 eq1493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493
  have eq1496 : False := by grind
  exact eq1496

/-- `Equation3352`: `x ◇ y = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pxy_pyy_pyx_Equation3352 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3352 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3352.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    grind
  have eq18 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    first
    | (have j0 := eq17 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq19 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq10 X0
       grind)
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    grind
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    first
    | (have j0 := eq20 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq22 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0
       grind)
    | exact resolve eq11 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : (M.op x y) = (M.op x y) := by grind
  have eq24 : (M.op x y) = (M.op x y) := by grind
  clear eq23
  have eq25 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq26 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq25
  have eq27 : (σ x) = (σ x) := by grind
  have eq28 : (σ x) = (σ x) := by grind
  clear eq27
  have eq29 : (σ y) = (σ y) := by grind
  have eq30 : (σ y) = (σ y) := by grind
  clear eq29
  have eq31 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq32 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq31
  have eq33 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq34 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq19 eq18
    | (have j1 := eq19 X0
       grind)
    | exact resolve eq18 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19
  have eq35 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq22 eq21
    | (have j1 := eq22 X0
       grind)
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq22
  have eq36 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq34
    | (have j0 := eq34 (M.op x y)
       grind)
    | exact resolve eq34 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq34 x
       have i₂ := eq28
       grind)
    | exact superpose eq28 eq34
    | (have j0 := eq34 x
       grind)
    | exact resolve eq34 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq40 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq34 y
       have i₂ := eq30
       grind)
    | exact superpose eq30 eq34
    | (have j0 := eq34 y
       grind)
    | exact resolve eq34 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq41 : (M.op x y) = (M.op (τ (σ x)) y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq38
       grind)
    | exact superpose eq38 eq24
    | exact resolve eq24 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq38
  have eq42 : (M.op x y) = (M.op (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq41
       have i₂ := eq40
       grind)
    | exact superpose eq40 eq41
    | exact resolve eq41 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq41
  have eq46 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq34
    | exact resolve eq34 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq47 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq46 (τ X0) X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq46
    | exact resolve eq46 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq9 X1 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq96 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq96 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq96 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq114 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X1 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq47
    | exact resolve eq47 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq131 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 (M.op X0 (M.op X1 X1))) ∨ (M.op X1 X1) = (M.op X0 (M.op X0 (M.op X1 X1))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq14
    | (have j0 := eq14 X0 X1
       grind)
    | exact resolve eq14 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 (M.op X0 (M.op X1 X1))) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 (M.op X0 (k X1 X1))) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq137 X0 X1
       have i₂ := eq97 X1
       grind)
    | exact superpose eq97 eq137
    | (have j0 := eq137 X0 X1
       grind)
    | exact resolve eq137 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq153 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq135
       have i₂ := eq97 sF4
       grind)
    | exact superpose eq97 eq135
    | exact resolve eq135 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq157 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 (M.op X0 (k X1 X1))) ∨ (M.op X1 X1) = (M.op X0 (M.op X0 (M.op X1 X1))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq131 X0 X1
       have i₂ := eq97 X1
       grind)
    | exact superpose eq97 eq131
    | (have j0 := eq131 X0 X1
       grind)
    | exact resolve eq131 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq164 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 (M.op X0 (k X1 X1))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq152 X0 X1
       have i₂ := eq97 X1
       grind)
    | exact superpose eq97 eq152
    | (have j0 := eq152 X0 X1
       grind)
    | exact resolve eq152 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq165 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq153
       have i₂ := eq97 sF4
       grind)
    | exact superpose eq97 eq153
    | exact resolve eq153 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq169 : ∀ X0 X1 : G, (k X1 X1) = (M.op X0 (M.op X0 (k X1 X1))) ∨ (k X0 X1) = (M.op X0 (M.op X0 (k X1 X1))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq157 X0 X0
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq157
    | (have j0 := eq157 X0 X1
       grind)
    | exact resolve eq157 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq176 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 (M.op X0 (k X1 X1))) ∨ (M.op X1 X0) = (k X1 X1) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq164 X0 X1
       have i₂ := eq97 X1
       grind)
    | exact superpose eq97 eq164
    | (have j0 := eq164 X0 X1
       grind)
    | exact resolve eq164 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq179 : ∀ X0 X1 : G, (k X1 X1) = (M.op X0 (M.op X0 (k X1 X1))) ∨ (k X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 (M.op X0 (k X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq169 X0 X1
       have i₂ := eq97 X1
       grind)
    | exact superpose eq97 eq169
    | (have j0 := eq169 X0 X1
       grind)
    | exact resolve eq169 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq304 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq13
    | exact resolve eq13 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq9
    | exact resolve eq9 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq165 eq33
    | exact resolve eq33 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq463 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X1) (M.op (M.op X1 X1) (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 X0
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq63
    | exact resolve eq63 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq481 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (k X1 X1) (M.op (k X1 X1) (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq463 X0 X0
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq463
    | exact resolve eq463 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq518 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq95
       have i₂ := eq97 sF4
       grind)
    | exact superpose eq97 eq95
    | exact resolve eq95 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq97
  have eq875 : ∀ X0 X1 : G, (k X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 ∨ (k X1 X0) = (M.op X1 (M.op X1 (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X1 X0
       have i₂ := eq179 X1 X0
       grind)
    | exact superpose eq179 eq176
    | (have j0 := eq176 X1 X0
       have j1 := eq179 X1 X0
       grind)
    | exact resolve eq176 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq879 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X1) ∨ (k X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 (M.op X0 (k X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq179 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq880 : ∀ X0 X1 : G, (k X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X0 X0) ∨ (k X0 X0) = X0 ∨ (k X1 X0) = (M.op X1 (M.op X1 (k X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq875 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875
  have eq886 : ∀ X0 X1 : G, (k X0 X0) = (k X1 X0) ∨ (k X0 X0) = X0 ∨ (k X1 X0) = (M.op X1 (M.op X1 (k X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq880 X0 X1
       have j1 := eq304 X0 X1
       grind)
    | (have r₁ := eq880 X0 X1
       have r₂ := eq304 X0 X1
       grind)
    | (have r₁ := eq880 X0 X0
       have r₂ := eq304 X0 (M.op X0 (k X0 X0))
       grind)
    | exact resolve eq880 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304 eq880
  have eq894 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 (M.op X1 (k X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq886 X0 X1
       have j1 := eq879 X1 X0
       grind)
    | (have r₁ := eq886 X1 X1
       have r₂ := eq879 X1 X1
       grind)
    | (have r₁ := eq886 X1 X0
       have r₂ := eq879 X0 X1
       grind)
    | exact resolve eq886 eq879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879 eq886
  have eq1491 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq306 X1 X0
       have i₂ := eq894 X1 X0
       grind)
    | exact superpose eq894 eq306
    | (have j1 := eq894 X1 X1
       grind)
    | exact resolve eq306 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1957 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (k (k X0 X0) X1)) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq481 X1 X0
       have i₂ := eq894 X1 (k X0 X0)
       grind)
    | exact superpose eq894 eq481
    | (have j1 := eq894 X1 X1
       grind)
    | exact resolve eq481 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481 eq894
  have eq27479 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq42
       have i₂ := eq1491 (τ sF5) (τ sF4)
       grind)
    | exact superpose eq1491 eq42
    | (have j1 := eq1491 x (τ (σ x))
       grind)
    | exact resolve eq42 eq1491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27889 : (σ (τ (σ x))) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq27479 eq15
    | exact resolve eq15 eq27479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27479
  have eq27891 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq27889
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq27889
    | exact resolve eq27889 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27889
  have eq27904 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq27891 eq15
    | exact resolve eq15 eq27891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27891
  have eq27905 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq27904
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq27904
    | exact resolve eq27904 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27904
  have eq27907 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq27905
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq27905
    | exact resolve eq27905 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27905
  have eq27908 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq27907
    | exact resolve eq27907 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27907
  have eq28533 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (k (σ x) X0)) ∨ (k X0 X0) = X0 ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq27908 eq1957
    | (have j0 := eq1957 X0 X0
       grind)
    | exact resolve eq1957 eq27908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28549 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27908 eq114
    | exact resolve eq114 eq27908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27908
  have eq29528 : ∀ X0 : G, (M.op (τ (σ x)) X0) = (M.op X0 (k (τ (σ x)) X0)) ∨ (k X0 X0) = X0 ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq28549 eq1957
    | (have j0 := eq1957 X0 X0
       grind)
    | exact resolve eq1957 eq28549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957 eq28549
  have eq65221 : ∀ X0 : G, (M.op (σ x) X0) = (k (k (σ x) X0) X0) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq28533 eq1491
    | (have j0 := eq1491 X0 X0
       have j1 := eq28533 X0
       grind)
    | exact resolve eq1491 eq28533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28533
  have eq65274 : ∀ X0 : G, (M.op (σ x) X0) = (k (k (σ x) X0) X0) ∨ (k X0 X0) = X0 ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq65221 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65221
  have eq66694 : (M.op (σ x) (σ y)) = (k (k (σ x) (σ y)) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq65274 eq32
    | (have j1 := eq65274 (σ y)
       grind)
    | exact resolve eq32 eq65274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65274
  have eq67466 : (σ (M.op x y)) ≠ (k (k (σ x) (σ y)) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq66694 eq33
    | exact resolve eq33 eq66694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66694
  have eq180409 : ∀ X0 : G, (M.op (τ (σ x)) X0) = (k (k (τ (σ x)) X0) X0) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq29528 eq1491
    | (have j0 := eq1491 X0 X0
       have j1 := eq29528 X0
       grind)
    | exact resolve eq1491 eq29528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29528
  have eq180434 : ∀ X0 : G, (M.op (τ (σ x)) X0) = (k (k (τ (σ x)) X0) X0) ∨ (k X0 X0) = X0 ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq180409 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180409
  have eq188259 : (M.op x y) = (k (k (τ (σ x)) (τ (σ y))) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq180434 eq42
    | (have j1 := eq180434 (τ (σ y))
       grind)
    | exact resolve eq42 eq180434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180434
  have eq353934 : (σ (M.op x y)) = (k (σ (k (τ (σ x)) (τ (σ y)))) (σ (τ (σ y)))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq188259 eq15
    | exact resolve eq15 eq188259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188259
  have eq353940 : (σ (M.op x y)) = (k (σ (k (τ (σ x)) (τ (σ y)))) (σ y)) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq353934
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq353934
    | exact resolve eq353934 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353934
  have eq353941 : (σ (M.op x y)) = (k (k (σ (τ (σ x))) (σ (τ (σ y)))) (σ y)) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq353940
       have i₂ := eq15 (τ sF4) (τ sF5)
       grind)
    | exact superpose eq15 eq353940
    | exact resolve eq353940 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353940
  have eq353942 : (σ (M.op x y)) = (k (k (σ (τ (σ x))) (σ y)) (σ y)) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq353941
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq353941
    | exact resolve eq353941 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353941
  have eq353943 : (σ (M.op x y)) = (k (k (σ x) (σ y)) (σ y)) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq353942
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq353942
    | exact resolve eq353942 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353942
  have eq353944 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (k (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq353943
    | exact resolve eq353943 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353943
  have eq354046 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (σ (M.op x y)) = (k (k (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq353944 eq15
    | exact resolve eq15 eq353944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353944
  have eq354110 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (k (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq354046
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq354046
    | exact resolve eq354046 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354046
  have eq354123 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq354110
       have r₂ := eq67466
       grind)
    | exact resolve eq354110 eq67466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67466 eq354110
  have eq354129 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq354123 eq305
    | (have j0 := eq305 (σ y) X0
       grind)
    | (have r₁ := eq305 (σ y) x
       have r₂ := eq354123
       grind)
    | exact resolve eq305 eq354123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354305 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq354123 eq114
    | exact resolve eq114 eq354123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354123
  have eq354376 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq354129 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354129
  have eq354682 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq354376 eq32
    | (have j1 := eq354376 (σ x)
       grind)
    | exact resolve eq32 eq354376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354376
  have eq354891 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq354682 eq33
    | exact resolve eq33 eq354682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354682
  have eq355515 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k X0 (τ (σ y))) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq354305 eq305
    | (have j0 := eq305 (τ (σ y)) X0
       grind)
    | (have r₁ := eq305 (τ (σ y)) x
       have r₂ := eq354305
       grind)
    | exact resolve eq305 eq354305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354305
  have eq355708 : ∀ X0 : G, (k X0 (τ (σ y))) = (M.op X0 (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq355515 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355515
  have eq357425 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq355708 eq42
    | exact resolve eq42 eq355708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355708
  have eq357588 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq357425 eq15
    | exact resolve eq15 eq357425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357425
  have eq357598 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq357588
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq357588
    | exact resolve eq357588 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357588
  have eq357600 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq357598
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq357598
    | exact resolve eq357598 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357598
  have eq357601 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq357600
    | exact resolve eq357600 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357600
  have eq357602 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq357601
       have r₂ := eq354891
       grind)
    | exact resolve eq357601 eq354891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354891 eq357601
  have eq357603 : (M.op x y) = (τ (k (σ y) (σ x))) := by
    first
    | exact superpose eq357602 eq36
    | exact resolve eq36 eq357602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq357611 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq357602 eq392
    | (have r₁ := eq392
       have r₂ := eq357602
       grind)
    | exact resolve eq392 eq357602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq357638 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by grind
  clear eq357611
  have eq357648 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq357603
       have i₂ := eq114 sF4 sF5
       grind)
    | exact superpose eq114 eq357603
    | exact resolve eq357603 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357603
  have eq357681 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) := by
    first
    | exact superpose eq357648 eq15
    | exact resolve eq15 eq357648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357690 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) := by
    first
    | (have i₁ := eq357681
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq357681
    | exact resolve eq357681 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357681
  have eq357691 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq357690
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq357690
    | exact resolve eq357690 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357690
  have eq357818 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq357638 eq33
    | exact resolve eq33 eq357638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357819 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq357638 eq518
    | (have r₁ := eq518
       have r₂ := eq357638
       grind)
    | exact resolve eq518 eq357638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq357638
  have eq357846 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by grind
  clear eq357819
  have eq357847 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by grind
  clear eq357846
  have eq357850 : (k (σ y) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq357602 eq357818
    | exact resolve eq357818 eq357602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357818
  have eq357851 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq357850
       have r₂ := eq357847
       grind)
    | exact resolve eq357850 eq357847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357847 eq357850
  have eq358336 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq357851 eq305
    | (have j0 := eq305 (σ x) X0
       grind)
    | (have r₁ := eq305 (σ x) x
       have r₂ := eq357851
       grind)
    | exact resolve eq305 eq357851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358337 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq357851 eq306
    | exact resolve eq306 eq357851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358579 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq357851 eq114
    | exact resolve eq114 eq357851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357851
  have eq358584 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq358336 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358336
  have eq359681 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = (M.op X0 (τ (σ x))) := by
    intro X0
    first
    | exact superpose eq358579 eq305
    | (have j0 := eq305 (τ (σ x)) X0
       grind)
    | (have r₁ := eq305 (τ (σ x)) x
       have r₂ := eq358579
       grind)
    | exact resolve eq305 eq358579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359682 : ∀ X0 : G, (M.op (τ (σ x)) X0) = (M.op X0 (M.op X0 (τ (σ x)))) := by
    intro X0
    first
    | exact superpose eq358579 eq306
    | exact resolve eq306 eq358579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq358579
  have eq359858 : ∀ X0 : G, (k X0 (τ (σ x))) = (M.op X0 (τ (σ x))) := by
    intro X0
    first
    | (have j0 := eq359681 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359681
  have eq359976 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (k X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq358584 eq358337
    | exact resolve eq358337 eq358584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358337 eq358584
  have eq361607 : ∀ X0 : G, (M.op (σ x) X0) = (k (k X0 (σ x)) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq359976 eq1491
    | (have j0 := eq1491 X0 X0
       grind)
    | exact resolve eq1491 eq359976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359976
  have eq363200 : ∀ X0 : G, (M.op (τ (σ x)) X0) = (M.op X0 (k X0 (τ (σ x)))) := by
    intro X0
    first
    | exact superpose eq359858 eq359682
    | exact resolve eq359682 eq359858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359682 eq359858
  have eq364747 : (M.op (τ (σ x)) (τ (σ y))) = (M.op (τ (σ y)) (M.op x y)) := by
    first
    | exact superpose eq357648 eq363200
    | exact resolve eq363200 eq357648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357648 eq363200
  have eq365113 : (M.op x y) = (M.op (τ (σ y)) (M.op x y)) := by
    first
    | exact superpose eq42 eq364747
    | exact resolve eq364747 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364747
  have eq365200 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq365113 eq1491
    | (have j0 := eq1491 x (τ (σ y))
       grind)
    | exact resolve eq1491 eq365113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1491 eq365113
  have eq371582 : (M.op (σ x) (σ y)) = (k (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq361607 eq32
    | (have j1 := eq361607 (σ y)
       grind)
    | exact resolve eq32 eq361607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361607
  have eq371917 : (σ (M.op x y)) ≠ (k (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq371582 eq33
    | exact resolve eq33 eq371582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371582
  have eq371964 : (k (σ y) (σ x)) ≠ (k (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq357602 eq371917
    | exact resolve eq371917 eq357602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371917
  have eq372772 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq365200 eq15
    | exact resolve eq15 eq365200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365200
  have eq372776 : (M.op x y) = (k (M.op x y) (τ (σ y))) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq372772
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq372772
    | exact resolve eq372772 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372772
  have eq372804 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (τ (σ y)))) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq372776 eq15
    | exact resolve eq15 eq372776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372776
  have eq372808 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq372804
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq372804
    | exact resolve eq372804 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372804
  have eq372809 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq372808
    | exact resolve eq372808 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq372808
  have eq372810 : (k (σ y) (σ x)) = (k (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq357602 eq372809
    | exact resolve eq372809 eq357602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372809
  have eq372811 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq372810
       have r₂ := eq371964
       grind)
    | exact resolve eq372810 eq371964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371964 eq372810
  have eq372818 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq372811 eq305
    | (have j0 := eq305 (σ y) X0
       grind)
    | (have r₁ := eq305 (σ y) x
       have r₂ := eq372811
       grind)
    | exact resolve eq305 eq372811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373045 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq372811 eq114
    | exact resolve eq114 eq372811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq372811
  have eq373048 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq372818 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372818
  have eq373452 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq373048 eq32
    | (have j1 := eq373048 (σ x)
       grind)
    | exact resolve eq32 eq373048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq373048
  have eq373499 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) := by
    first
    | exact superpose eq373452 eq33
    | exact resolve eq33 eq373452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq373452
  have eq373535 : (k (σ y) (σ x)) ≠ (k (σ x) (σ y)) := by
    first
    | exact superpose eq357602 eq373499
    | exact resolve eq373499 eq357602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357602 eq373499
  have eq373991 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k X0 (τ (σ y))) = (M.op X0 (τ (σ y))) := by
    intro X0
    first
    | exact superpose eq373045 eq305
    | (have j0 := eq305 (τ (σ y)) X0
       grind)
    | (have r₁ := eq305 (τ (σ y)) x
       have r₂ := eq373045
       grind)
    | exact resolve eq305 eq373045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq373045
  have eq374171 : ∀ X0 : G, (k X0 (τ (σ y))) = (M.op X0 (τ (σ y))) := by
    intro X0
    first
    | (have j0 := eq373991 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373991
  have eq375518 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) := by
    first
    | exact superpose eq374171 eq42
    | exact resolve eq42 eq374171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq374171
  have eq375577 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ y)))) := by
    first
    | exact superpose eq375518 eq15
    | exact resolve eq15 eq375518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375518
  have eq375582 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ y)) := by
    first
    | (have i₁ := eq375577
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq375577
    | exact resolve eq375577 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375577
  have eq375583 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq375582
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq375582
    | exact resolve eq375582 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq375582
  have eq375586 : (k (σ y) (σ x)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq375583 eq357691
    | exact resolve eq357691 eq375583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357691 eq375583
  have eq375673 : False := by grind
  exact eq375673

/-- `Equation3352`: `x ◇ y = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pyx_pxy_Equation3352 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3352 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3352.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 (M.op X0 X0))) := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq50 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq70 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq72 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq70 (σ X0)
       grind)
    | exact superpose eq70 eq10
    | exact resolve eq10 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq70 sF2
       grind)
    | exact superpose eq70 eq50
    | exact resolve eq50 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq75 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq74
       have i₂ := eq70 x
       grind)
    | exact superpose eq70 eq74
    | exact resolve eq74 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq72 X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq72
    | exact resolve eq72 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq84 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq68
       have i₂ := eq70 sF3
       grind)
    | exact superpose eq70 eq68
    | exact resolve eq68 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq85 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq84
       have i₂ := eq70 y
       grind)
    | exact superpose eq70 eq84
    | exact resolve eq84 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq98
    | exact resolve eq98 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq108 : ∀ X0 : G, (σ (k X0 (M.op y y))) = (k (σ X0) (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (M.op y y)
       have i₂ := eq85
       grind)
    | exact superpose eq85 eq10
    | exact resolve eq10 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq85
       grind)
    | exact superpose eq85 eq16
    | exact resolve eq16 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : (σ (k (k x x) y)) = (k (k (σ x) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq41 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq41
    | exact resolve eq41 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq193 : (k (M.op (σ x) (σ x)) (σ y)) = (σ (k (k x x) y)) := by
    first
    | (have i₁ := eq180
       have i₂ := eq70 sF2
       grind)
    | exact superpose eq70 eq180
    | exact resolve eq180 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq195 : (σ (k (M.op x x) y)) = (k (M.op (σ x) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq193
       have i₂ := eq70 x
       grind)
    | exact superpose eq70 eq193
    | exact resolve eq193 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq262 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 X0 (τ X0)
       have i₂ := eq70 (τ X0)
       grind)
    | exact superpose eq70 eq35
    | exact resolve eq35 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq273 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq262 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq262
    | exact resolve eq262 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq275 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq273 X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq273
    | exact resolve eq273 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq360 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq397 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq77 (M.op y y)
       have i₂ := eq85
       grind)
    | exact superpose eq85 eq77
    | exact resolve eq77 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq14
    | exact resolve eq14 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq475 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq266 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq266
    | exact resolve eq266 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq489 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq266 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq266
    | (have j0 := eq266 X0 y
       grind)
    | exact resolve eq266 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq541 : (k (M.op y y) y) = (τ (k (M.op (σ y) (σ y)) (σ y))) := by
    first
    | exact superpose eq110 eq489
    | exact resolve eq489 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq8164 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq8165 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq8164
    | exact resolve eq8164 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8164
  have eq8176 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq8165
       have r₂ := eq28
       grind)
    | exact resolve eq8165 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8165
  have eq8180 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq8176 eq110
    | exact resolve eq110 eq8176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8176
  have eq8202 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq8180
    | exact resolve eq8180 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8180
  have eq8203 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8202
  have eq8206 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq85
       have i₂ := eq8203
       grind)
    | exact superpose eq8203 eq85
    | exact resolve eq85 eq8203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8213 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq8203
       grind)
    | exact superpose eq8203 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq8203
       grind)
    | exact resolve eq13 eq8203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8216 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq416 y X0
       have i₂ := eq8203
       grind)
    | exact superpose eq8203 eq416
    | (have j0 := eq416 y X0
       grind)
    | exact resolve eq416 eq8203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq8219 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq8216 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8216
  have eq8220 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq8213 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8213
  have eq8223 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8219 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8219
    | (have j0 := eq8219 X0
       grind)
    | exact resolve eq8219 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8219
  have eq8230 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq8206
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8206
    | exact resolve eq8206 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8206
  have eq8240 : (k (M.op y y) y) = (τ (k (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8230 eq541
    | exact resolve eq541 eq8230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq8252 : (τ (M.op (σ y) (σ y))) = (k (M.op y y) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq8240
       have i₂ := eq70 sF3
       grind)
    | exact superpose eq70 eq8240
    | exact resolve eq8240 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq8240
  have eq8258 : (M.op y y) = (k (M.op y y) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq110 eq8252
    | exact resolve eq8252 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq8252
  have eq8381 : (k (M.op (σ x) (σ x)) (σ y)) = (σ (M.op y (M.op x x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq195
       have i₂ := eq8220 (M.op x x)
       grind)
    | exact superpose eq8220 eq195
    | exact resolve eq195 eq8220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8418 : ∀ X0 : G, (k X0 (τ y)) = (τ (M.op y (σ X0))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq360 X0 y
       have i₂ := eq8220 (σ X0)
       grind)
    | exact superpose eq8220 eq360
    | exact resolve eq360 eq8220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360 eq8220
  have eq8427 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq41 eq8223
    | exact resolve eq8223 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq8223
  have eq10358 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (M.op (σ y) (σ (k (M.op X0 X0) y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq8427 eq417
    | exact resolve eq417 eq8427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417 eq8427
  have eq10971 : ∀ X0 : G, (k (τ X0) (τ y)) = (τ (M.op y X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8418 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq8418
    | exact resolve eq8418 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8418
  have eq11108 : ∀ X0 : G, (τ (M.op y X0)) = (τ (k X0 y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10971 X0
       have i₂ := eq475 y X0
       grind)
    | exact superpose eq475 eq10971
    | exact resolve eq10971 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475 eq10971
  have eq11317 : (τ (M.op y (M.op y y))) = (τ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11108 (M.op y y)
       have i₂ := eq8258
       grind)
    | exact superpose eq8258 eq11108
    | exact resolve eq11108 eq8258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8258 eq11108
  have eq11360 : (τ (M.op y (M.op y y))) = (τ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11317
  have eq16346 : (τ y) = (τ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11360
       have i₂ := eq8203
       grind)
    | exact superpose eq8203 eq11360
    | exact resolve eq11360 eq8203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11360
  have eq16402 : (τ y) = (τ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq16346
  have eq16462 : (M.op (M.op y y) (M.op y y)) = (σ (M.op (τ y) (τ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq275 (M.op y y)
       have i₂ := eq16402
       grind)
    | exact superpose eq16402 eq275
    | exact resolve eq275 eq16402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16402
  have eq16534 : (M.op y y) = (M.op (M.op y y) (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16462
       have i₂ := eq275 y
       grind)
    | exact superpose eq275 eq16462
    | exact resolve eq16462 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq16462
  have eq26171 : ∀ X0 : G, (M.op y y) ≠ (M.op y y) ∨ (k X0 (M.op y y)) = (M.op (M.op y y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op y y)
       have i₂ := eq16534
       grind)
    | exact superpose eq16534 eq13
    | (have j0 := eq13 X0 (M.op y y)
       grind)
    | (have r₁ := eq13 X0 (M.op y y)
       have r₂ := eq16534
       grind)
    | exact resolve eq13 eq16534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26172 : ∀ X0 : G, (M.op (M.op y y) X0) = (M.op X0 (M.op X0 (M.op y y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14 (M.op y y) X0
       have i₂ := eq16534
       grind)
    | exact superpose eq16534 eq14
    | exact resolve eq14 eq16534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16534
  have eq26178 : ∀ X0 : G, (k X0 (M.op y y)) = (M.op (M.op y y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq26171 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26171
  have eq26184 : ∀ X0 : G, (M.op (M.op y y) X0) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq26172 X0
       have i₂ := eq14 y X0
       grind)
    | exact superpose eq14 eq26172
    | exact resolve eq26172 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26172
  have eq27139 : (σ (M.op y y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq397
       have i₂ := eq8203
       grind)
    | exact superpose eq8203 eq397
    | exact resolve eq397 eq8203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq8203
  have eq27234 : (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq27139
       have i₂ := eq85
       grind)
    | exact superpose eq85 eq27139
    | exact resolve eq27139 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq27139
  have eq27246 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (k X0 (M.op (σ y) (σ y))) = (M.op (M.op (σ y) (σ y)) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27234 eq13
    | (have j0 := eq13 X0 (M.op (σ y) (σ y))
       grind)
    | (have r₁ := eq13 X0 (M.op (σ y) (σ y))
       have r₂ := eq27234
       grind)
    | exact resolve eq13 eq27234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27234
  have eq27254 : ∀ X0 : G, (k X0 (M.op (σ y) (σ y))) = (M.op (M.op (σ y) (σ y)) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq27246 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27246
  have eq27267 : ∀ X0 : G, (σ (k X0 (M.op y y))) = (M.op (M.op (σ y) (σ y)) (σ X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq108 eq27254
    | exact resolve eq27254 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq27254
  have eq294458 : (M.op (σ x) (σ y)) = (M.op (σ y) (k (M.op (σ x) (σ x)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10358 x
       have i₂ := eq195
       grind)
    | exact superpose eq195 eq10358
    | exact resolve eq10358 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq10358
  have eq294520 : (M.op (σ x) (σ y)) = (M.op (σ y) (k (M.op (σ x) (σ x)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq294458
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq294458
    | exact resolve eq294458 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294458
  have eq294536 : (M.op (σ x) (σ y)) = (M.op (σ y) (k (M.op (σ x) (σ x)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq294520
    | exact resolve eq294520 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294520
  have eq336401 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (k X0 (M.op y y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq8230 eq27267
    | exact resolve eq27267 eq8230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8230 eq27267
  have eq337156 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (k X0 (M.op y y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq336401 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336401
  have eq337190 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (M.op (M.op y y) X0)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq337156 X0
       have i₂ := eq26178 X0
       grind)
    | exact superpose eq26178 eq337156
    | exact resolve eq337156 eq26178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26178 eq337156
  have eq337499 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (M.op (M.op y y) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq337190 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337190
  have eq347160 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (M.op y X0)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq337499 X0
       have i₂ := eq26184 X0
       grind)
    | exact superpose eq26184 eq337499
    | exact resolve eq337499 eq26184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26184 eq337499
  have eq347427 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (M.op y X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq347160 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347160
  have eq347525 : (M.op (σ y) (k (M.op (σ x) (σ x)) (σ y))) = (σ (M.op y (M.op y (M.op x x)))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq347427 (M.op y (M.op x x))
       have i₂ := eq8381
       grind)
    | exact superpose eq8381 eq347427
    | exact resolve eq347427 eq8381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8381 eq347427
  have eq348282 : (M.op (σ y) (k (M.op (σ x) (σ x)) (σ y))) = (σ (M.op y (M.op y (M.op x x)))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq347525
  have eq348339 : (σ (M.op x y)) = (M.op (σ y) (k (M.op (σ x) (σ x)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq348282
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq348282
    | exact resolve eq348282 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348282
  have eq348356 : (σ (M.op x y)) = (M.op (σ y) (k (M.op (σ x) (σ x)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq348339
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq348339
    | exact resolve eq348339 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348339
  have eq348357 : (σ (M.op x y)) = (M.op (σ y) (k (M.op (σ x) (σ x)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq348356
    | exact resolve eq348356 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348356
  have eq349115 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq348357 eq294536
    | exact resolve eq294536 eq348357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294536 eq348357
  have eq349118 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq349115
  have eq349123 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq349118
       have r₂ := eq28
       grind)
    | exact resolve eq349118 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349118
  have eq349132 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq349123 eq30
    | exact resolve eq30 eq349123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq349123
  have eq349280 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq349132
    | exact resolve eq349132 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq349132
  have eq349281 : x = y := by grind
  clear eq349280
  have eq349303 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq349281
       grind)
    | exact superpose eq349281 eq19
    | exact resolve eq19 eq349281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq349304 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq349281
       grind)
    | exact superpose eq349281 eq25
    | exact resolve eq25 eq349281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq349281
  have eq349629 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq349304
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq349304
    | exact resolve eq349304 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq349304
  have eq349658 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq349629 eq27
    | exact resolve eq27 eq349629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq349629
  have eq349925 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq349658 eq75
    | exact resolve eq75 eq349658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq349658
  have eq349964 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq349925
       have i₂ := eq349303
       grind)
    | exact superpose eq349303 eq349925
    | exact resolve eq349925 eq349303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349303 eq349925
  have eq349971 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq349964 eq15
    | exact resolve eq15 eq349964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349964
  have eq350528 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq349971
    | exact resolve eq349971 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq349971
  have eq350676 : False := by grind
  exact eq350676

/-- `Equation3352`: `x ◇ y = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation3352 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3352 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3352.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq449 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq452 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq632 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq452 x y
       grind)
    | exact superpose eq452 eq16
    | (have j1 := eq452 x y
       grind)
    | exact resolve eq16 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq452 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq3086 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq449 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq449
    | exact resolve eq449 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq3129 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3086 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3086
    | (have j0 := eq3086 X0 X1
       grind)
    | exact resolve eq3086 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3086
  have eq3288 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq632
       have i₂ := eq3129 y x
       grind)
    | exact superpose eq3129 eq632
    | (have j1 := eq3129 (σ x) (σ y)
       grind)
    | (have r₁ := eq632
       have r₂ := eq3129 y x
       grind)
    | (have r₁ := eq632
       have r₂ := eq3129 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq632
       have r₂ := eq3129 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq632 eq3129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3289 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq3288
  have eq7915 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) ≠ (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq639 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq639
    | exact resolve eq639 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq7945 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7915 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq7915
    | (have j0 := eq7915 X0 X1
       grind)
    | exact resolve eq7915 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq7915
  have eq7950 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7945 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7945
    | exact resolve eq7945 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7945
  have eq19025 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3289
       grind)
    | exact superpose eq3289 eq16
    | exact resolve eq16 eq3289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3289
  have eq19026 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq19025
       have r₂ := eq22 x
       grind)
    | exact resolve eq19025 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19025
  have eq19028 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19026
       grind)
    | exact superpose eq19026 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19026
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19026
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19026
       grind)
    | exact resolve eq13 eq19026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19026
  have eq19029 : x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq19028
  have eq19250 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19029
       grind)
    | exact superpose eq19029 eq16
    | exact resolve eq16 eq19029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19029
  have eq19251 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq19250
       have r₂ := eq22 x
       grind)
    | exact resolve eq19250 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19250
  have eq19253 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq19251
       grind)
    | exact superpose eq19251 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19251
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19251
       grind)
    | exact resolve eq13 eq19251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19251
  have eq19257 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by grind
  clear eq19253
  have eq19258 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by grind
  clear eq19257
  have eq19261 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq19258
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq19258
    | exact resolve eq19258 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19258
  have eq19295 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19261
       grind)
    | exact superpose eq19261 eq16
    | exact resolve eq16 eq19261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19261
  have eq19323 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq19295
       have i₂ := eq3129 y x
       grind)
    | exact superpose eq3129 eq19295
    | (have j1 := eq3129 x y
       grind)
    | (have r₁ := eq19295
       have r₂ := eq3129 y x
       grind)
    | (have r₁ := eq19295
       have r₂ := eq3129 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq19295
       have r₂ := eq3129 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq19295 eq3129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3129 eq19295
  have eq19324 : (σ x) = (σ y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq19323
  have eq19326 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq7950 x y
       grind)
    | (have r₁ := eq19324
       have r₂ := eq7950 x y
       grind)
    | exact resolve eq19324 eq7950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7950 eq19324
  have eq19328 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq19326
       grind)
    | exact superpose eq19326 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19326
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19326
       grind)
    | exact resolve eq13 eq19326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19329 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19326
       grind)
    | exact superpose eq19326 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19326
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19326
       grind)
    | exact resolve eq13 eq19326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19326
  have eq19330 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq19329
  have eq19331 : x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq19330
  have eq19332 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq19328
  have eq19333 : x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq19332
  have eq19334 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19331
       grind)
    | exact superpose eq19331 eq16
    | exact resolve eq16 eq19331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19331
  have eq19335 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq19334
       have r₂ := eq22 x
       grind)
    | exact resolve eq19334 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19334
  have eq19389 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19333
       grind)
    | exact superpose eq19333 eq16
    | exact resolve eq16 eq19333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19333
  have eq19390 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq19389
       have r₂ := eq22 x
       grind)
    | exact resolve eq19389 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19389
  have eq19392 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq632
       have i₂ := eq19390
       grind)
    | exact superpose eq19390 eq632
    | exact resolve eq632 eq19390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632 eq19390
  have eq19396 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq19392
  have eq19397 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq19396
  have eq19402 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq19397
       grind)
    | exact superpose eq19397 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19397
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19397
       grind)
    | exact resolve eq13 eq19397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19397
  have eq19403 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq19402
  have eq19404 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq19403
  have eq19408 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19404
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq19404
    | exact resolve eq19404 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19404
  have eq19414 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19408
       grind)
    | exact superpose eq19408 eq16
    | exact resolve eq16 eq19408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19408
  have eq19644 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19414
       have i₂ := eq19335
       grind)
    | exact superpose eq19335 eq19414
    | exact resolve eq19414 eq19335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19335 eq19414
  have eq19647 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq19644
  have eq19648 : (σ x) = (σ y) := by grind
  clear eq19647
  have eq19649 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19648
       grind)
    | exact superpose eq19648 eq16
    | exact resolve eq16 eq19648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19650 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq19648
       grind)
    | exact superpose eq19648 eq10
    | exact resolve eq10 eq19648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19648
  have eq19808 : x = y := by
    first
    | (have i₁ := eq19650
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19650
    | exact resolve eq19650 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19650
  have eq19809 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq19649
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq19649
    | exact resolve eq19649 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq19649
  have eq19810 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq19809
       have i₂ := eq19808
       grind)
    | exact superpose eq19808 eq19809
    | exact resolve eq19809 eq19808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19808 eq19809
  have eq19811 : False := by grind
  exact eq19811

/-- `Equation3491`: `x ◇ x = y ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_y_pxy_pxx_pxy_Equation3491 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3491 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3491.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  clear eq17
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
  clear eq22
  have eq62 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X0) (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) X0) X2 x
       have i₂ := eq9 X0 (M.op x (M.op (M.op X1 X0) X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq62 X0 x X2
       have i₂ := eq9 X0 (M.op (M.op x X0) X0) x
       grind)
    | (have i₁ := eq62 X0 x X2
       have i₂ := eq9 (M.op (M.op x X0) X0) x X2
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq75 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq75 (σ X0)
       grind)
    | exact superpose eq75 eq15
    | exact resolve eq15 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq75 (τ X0)
       grind)
    | exact superpose eq75 eq31
    | exact resolve eq31 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq89 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq82
    | exact resolve eq82 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq80 X0
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq80
    | exact resolve eq80 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq80
  have eq107 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (σ X0) x
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq63
    | exact resolve eq63 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1116 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) ≠ (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq107 X1 (σ X0)
       grind)
    | exact superpose eq107 eq15
    | (have j1 := eq107 X1 (σ X0)
       grind)
    | exact resolve eq15 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq3242 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq3269 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3242 X0 X1
       have i₂ := eq91 X1
       grind)
    | exact superpose eq91 eq3242
    | (have j0 := eq3242 X0 X1
       grind)
    | exact resolve eq3242 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3242
  have eq3283 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3269 X0 X1
       have i₂ := eq91 X1
       grind)
    | exact superpose eq91 eq3269
    | (have j0 := eq3269 X0 X1
       grind)
    | exact resolve eq3269 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq3269
  have eq3296 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3283 X0 X1
       have j1 := eq1116 X0 X1
       grind)
    | (have r₁ := eq3283 X0 X1
       have r₂ := eq1116 X0 X1
       grind)
    | exact resolve eq3283 eq1116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116 eq3283
  have eq4728 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X0 X0))) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3296 X1 (τ X0)
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq3296
    | (have j0 := eq3296 X1 (τ X0)
       grind)
    | exact resolve eq3296 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq4756 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq3296 X1 X0
       grind)
    | exact superpose eq3296 eq10
    | (have j1 := eq3296 X1 X0
       grind)
    | exact resolve eq10 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3296
  have eq4801 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4756 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4756
    | (have j0 := eq4756 X0 X1
       grind)
    | exact resolve eq4756 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4756
  have eq4806 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X0)) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4728 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4728
    | (have j0 := eq4728 X0 X1
       grind)
    | exact resolve eq4728 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4728
  have eq4810 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4806 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4806
    | (have j0 := eq4806 X0 X1
       grind)
    | exact resolve eq4806 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4806
  have eq4811 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4810 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4810
    | (have j0 := eq4810 X0 X1
       grind)
    | exact resolve eq4810 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4810
  have eq4812 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4811 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq4811
    | (have j0 := eq4811 X0 X1
       grind)
    | exact resolve eq4811 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4811
  have eq4813 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4812 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4812
    | (have j0 := eq4812 X1 X1
       grind)
    | exact resolve eq4812 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4812
  have eq5015 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4801 y x
       grind)
    | exact superpose eq4801 eq16
    | (have j1 := eq4801 y x
       grind)
    | exact resolve eq16 eq4801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4801
  have eq5284 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq5015
       have i₂ := eq4813 x y
       grind)
    | exact superpose eq4813 eq5015
    | (have j1 := eq4813 x y
       grind)
    | exact resolve eq5015 eq4813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4813 eq5015
  have eq5288 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) := by grind
  clear eq5284
  have eq5289 : y = (M.op y y) := by grind
  clear eq5288
  have eq5292 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq63 y x
       have i₂ := eq5289
       grind)
    | exact superpose eq5289 eq63
    | exact resolve eq63 eq5289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq5296 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq108 y x
       have i₂ := eq5289
       grind)
    | exact superpose eq5289 eq108
    | exact resolve eq108 eq5289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq5289
  have eq5685 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5296 (σ x)
       grind)
    | exact superpose eq5296 eq16
    | exact resolve eq16 eq5296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5296
  have eq5687 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq5685
       have i₂ := eq5292 x
       grind)
    | exact superpose eq5292 eq5685
    | exact resolve eq5685 eq5292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5292 eq5685
  have eq5688 : False := by grind
  exact eq5688
