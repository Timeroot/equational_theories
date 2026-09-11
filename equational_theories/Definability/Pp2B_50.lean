import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_x_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
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
  have eq54 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
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
  have eq66 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ X1 ∨ (k X3 X1) = (M.op X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X3 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : x ≠ (M.op x y) ∨ y = (M.op y y) ∨ x = (k x y) := by
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
  have eq77 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq95
    | (have j0 := eq95 (σ x) (σ X0)
       grind)
    | exact resolve eq95 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq95 x y
       grind)
    | exact superpose eq95 eq44
    | (have j1 := eq95 x y
       grind)
    | exact resolve eq44 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
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
  have eq120 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq118
    | exact resolve eq118 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq120
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq120
    | exact resolve eq120 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq121 eq95
    | (have j0 := eq95 (σ x) (σ y)
       grind)
    | exact resolve eq95 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq124
    | exact resolve eq124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq125
       have r₂ := eq27
       grind)
    | exact resolve eq125 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq130 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq128
    | exact resolve eq128 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq132 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq130 eq27
    | exact resolve eq27 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
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
  have eq767 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq130 eq77
    | (have r₁ := eq77
       have r₂ := eq130
       grind)
    | exact resolve eq77 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq130
  have eq768 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq767
  have eq1269 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op X0 (M.op X0 X0)))) ≠ X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq66 X1 X2 X1 X3
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq66
    | (have j0 := eq66 X0 X2 X2 X3
       grind)
    | exact resolve eq66 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq66
  have eq1328 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X0)) ≠ X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1269 X0 X1 X2 X3
       have i₂ := eq54 X0 X0 X2
       grind)
    | exact superpose eq54 eq1269
    | (have j0 := eq1269 X0 X1 X2 X3
       grind)
    | exact resolve eq1269 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1269
  have eq3151 : ∀ X0 : G, (σ x) = (k (σ x) (σ y)) ∨ (M.op X0 X0) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq768
       have i₂ := eq280 sF3 x
       grind)
    | (have i₁ := eq768
       have i₂ := eq280 X0 sF3
       grind)
    | exact superpose eq280 eq768
    | exact resolve eq768 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq3193 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (M.op X0 X0) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3151 eq121
    | (have j1 := eq3151 X0
       grind)
    | exact resolve eq121 eq3151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3151
  have eq3197 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq3193 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3193
  have eq3202 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3197 X0
       grind)
    | (have r₁ := eq3197 X0
       have r₂ := eq132
       grind)
    | exact resolve eq3197 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq3197
  have eq3279 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op x x) x x
       have i₂ := eq3202 (M.op x x)
       grind)
    | exact superpose eq3202 eq14
    | exact resolve eq14 eq3202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3202
  have eq3457 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3279 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq3279 (σ y)
       grind)
    | exact resolve eq13 eq3279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3279
  have eq3488 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3457 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3457
  have eq6306 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3488 eq121
    | exact resolve eq121 eq3488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq3488
  have eq6311 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq6306
  have eq6318 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq6311
    | exact resolve eq6311 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6311
  have eq6320 : x = (M.op x y) := by
    first
    | (have r₁ := eq6318
       have r₂ := eq27
       grind)
    | exact resolve eq6318 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6318
  have eq6322 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq6320 eq20
    | exact resolve eq20 eq6320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq6326 : x ≠ x ∨ y = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq6320 eq76
    | (have r₁ := eq76
       have r₂ := eq6320
       grind)
    | exact resolve eq76 eq6320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq6333 : y = (M.op y y) ∨ x = (k x y) := by grind
  clear eq6326
  have eq6339 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq6322
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6322
    | exact resolve eq6322 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6322
  have eq6341 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq6339 eq26
    | exact resolve eq26 eq6339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq9629 : ∀ X0 : G, x = (k x y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq6333
       have i₂ := eq280 y X0
       grind)
    | (have i₁ := eq6333
       have i₂ := eq280 X0 y
       grind)
    | exact superpose eq280 eq6333
    | exact resolve eq6333 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280 eq6333
  have eq10090 : ∀ X0 : G, (σ x) = (k (σ x) (σ y)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq44
       have i₂ := eq9629 X0
       grind)
    | exact superpose eq9629 eq44
    | (have j1 := eq9629 X0
       grind)
    | exact resolve eq44 eq9629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9629
  have eq10097 : ∀ X0 : G, (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | exact superpose eq6339 eq10090
    | (have j0 := eq10090 X0
       grind)
    | exact resolve eq10090 eq6339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10090
  have eq10099 : ∀ X0 : G, (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq10097 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10097
    | (have j0 := eq10097 X0
       grind)
    | exact resolve eq10097 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10097
  have eq10100 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | exact superpose eq6339 eq10099
    | (have j0 := eq10099 X0
       grind)
    | exact resolve eq10099 eq6339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10099
  have eq10160 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | exact superpose eq10100 eq95
    | (have j0 := eq95 (σ (M.op x y)) (σ y)
       have j1 := eq10100 X0
       grind)
    | exact resolve eq95 eq10100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq10100
  have eq10161 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq10160 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10160
  have eq10163 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | exact superpose eq6341 eq10161
    | (have j0 := eq10161 X0
       grind)
    | exact resolve eq10161 eq6341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10161
  have eq10166 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq10163 X0
       grind)
    | (have r₁ := eq10163 X0
       have r₂ := eq27
       grind)
    | exact resolve eq10163 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10163
  have eq10294 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op x x) x x
       have i₂ := eq10166 (M.op x x)
       grind)
    | exact superpose eq10166 eq14
    | exact resolve eq14 eq10166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10333 : y = (M.op x y) := by
    first
    | (have i₁ := eq51 sF0
       have i₂ := eq10166 sF0
       grind)
    | exact superpose eq10166 eq51
    | exact resolve eq51 eq10166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq10368 : y = (M.op x y) := by
    first
    | (have i₁ := eq10333
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10333
    | exact resolve eq10333 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq10333
  have eq10422 : x = y := by
    first
    | exact superpose eq6320 eq10368
    | exact resolve eq10368 eq6320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6320 eq10368
  have eq10455 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq10422
       grind)
    | exact superpose eq10422 eq24
    | exact resolve eq24 eq10422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10479 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq10455
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10455
    | exact resolve eq10455 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10455
  have eq10486 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq6339 eq10479
    | exact resolve eq10479 eq6339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10479
  have eq10567 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq10294 X0
       have i₂ := eq10422
       grind)
    | exact superpose eq10422 eq10294
    | exact resolve eq10294 eq10422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10294
  have eq10606 : ∀ X1 X2 X3 : G, (M.op X1 y) ≠ X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq1328 x X1 X2 X3
       have i₂ := eq10166 x
       grind)
    | exact superpose eq10166 eq1328
    | (have j0 := eq1328 x X1 X2 X3
       grind)
    | (have r₁ := eq1328 x (M.op x x) y X3
       have r₂ := eq10166 (M.op x x)
       grind)
    | exact resolve eq1328 eq10166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328 eq10166
  have eq10607 : ∀ X1 X2 X3 : G, (M.op X1 x) ≠ X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq10606 X1 X2 X3
       have i₂ := eq10422
       grind)
    | exact superpose eq10422 eq10606
    | (have j0 := eq10606 X1 X2 X3
       grind)
    | exact resolve eq10606 eq10422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10422 eq10606
  have eq10713 : ∀ X2 X3 : G, x ≠ X2 ∨ (k X3 X2) = (M.op X3 X2) := by
    intro X2 X3
    first
    | (have i₁ := eq10607 x X2 X3
       have i₂ := eq10567 x
       grind)
    | exact superpose eq10567 eq10607
    | (have j0 := eq10607 x X2 X3
       grind)
    | (have r₁ := eq10607 x x X3
       have r₂ := eq10567 x
       grind)
    | exact resolve eq10607 eq10567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10607
  have eq10714 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq10713 x X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10713
  have eq10715 : ∀ X0 : G, x = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq10714 X0
       have i₂ := eq10567 X0
       grind)
    | exact superpose eq10567 eq10714
    | exact resolve eq10714 eq10567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10567 eq10714
  have eq10729 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 x
       have i₂ := eq10715 (τ X0)
       grind)
    | exact superpose eq10715 eq34
    | exact resolve eq34 eq10715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq10715
  have eq10733 : ∀ X0 : G, (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10729 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10729
    | (have j0 := eq10729 X0
       grind)
    | exact resolve eq10729 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq10729
  have eq10743 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq6339 eq10733
    | exact resolve eq10733 eq6339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10733
  have eq10810 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq6339 eq100
    | (have j0 := eq100 X0
       grind)
    | exact resolve eq100 eq6339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq10811 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq6339 eq10810
    | (have j0 := eq10810 X0
       grind)
    | exact resolve eq10810 eq6339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6339 eq10810
  have eq10833 : (σ (k x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq10811 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10811
    | (have j0 := eq10811 y
       grind)
    | exact resolve eq10811 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq10811
  have eq10856 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq6341 eq10833
    | exact resolve eq10833 eq6341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10833
  have eq10885 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq10856
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq10856
    | exact resolve eq10856 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq10856
  have eq10909 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq10486 eq10885
    | exact resolve eq10885 eq10486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10486 eq10885
  have eq10932 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq10743 eq10909
    | exact resolve eq10909 eq10743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10743 eq10909
  have eq10951 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq10932
       have r₂ := eq27
       grind)
    | exact resolve eq10932 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10932
  have eq10967 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6341 eq10951
    | exact resolve eq10951 eq6341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6341 eq10951
  have eq10983 : False := by grind
  exact eq10983

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_x_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
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
  clear eq22
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
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
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
  have eq95 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq95 x y
       grind)
    | exact superpose eq95 eq44
    | (have j1 := eq95 x y
       grind)
    | exact resolve eq44 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq120 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq118
    | exact resolve eq118 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq120
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq120
    | exact resolve eq120 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq121 eq95
    | (have j0 := eq95 (σ x) (σ y)
       grind)
    | exact resolve eq95 eq121
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
  have eq233 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq130 eq52
    | exact resolve eq52 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq247 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq233
    | (have j0 := eq233 (σ x)
       grind)
    | exact resolve eq233 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq130 eq247
    | exact resolve eq247 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq263 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq259
  have eq264 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq263
    | exact resolve eq263 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq271 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op (σ x) (M.op X0 (σ y)))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1
       have i₂ := eq233 X0
       grind)
    | exact superpose eq233 eq55
    | exact resolve eq55 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq275 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
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
  have eq291 : ∀ X1 : G, (M.op X1 X1) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq271 X1 X1
       have i₂ := eq14 sF2 X1 sF3
       grind)
    | exact superpose eq14 eq271
    | exact resolve eq271 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq315 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq264
       have i₂ := eq291 sF2
       grind)
    | exact superpose eq291 eq264
    | exact resolve eq264 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq291
  have eq320 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq315 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq344 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op x x) x x
       have i₂ := eq320 (M.op x x)
       grind)
    | exact superpose eq320 eq14
    | exact resolve eq14 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq378 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq130 eq344
    | exact resolve eq344 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq344
  have eq395 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq378 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq428 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq395 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq395 (σ y)
       grind)
    | exact resolve eq13 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq439 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq428 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq466 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq3282 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq439 eq121
    | exact resolve eq121 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq439
  have eq3286 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3282
  have eq3289 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq3286
    | exact resolve eq3286 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3286
  have eq3291 : y = (M.op x y) := by
    first
    | (have r₁ := eq3289
       have r₂ := eq27
       grind)
    | exact resolve eq3289 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3289
  have eq3294 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq3291 eq20
    | exact resolve eq20 eq3291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq3296 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq3291 eq51
    | exact resolve eq51 eq3291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq3308 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq3294
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3294
    | exact resolve eq3294 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3294
  have eq3309 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq3308 eq26
    | exact resolve eq26 eq3308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq3557 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq3296 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3296
    | (have j0 := eq3296 x
       grind)
    | exact resolve eq3296 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3296
  have eq3643 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq3291 eq3557
    | exact resolve eq3557 eq3291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3557
  have eq3651 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3643
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3643
    | exact resolve eq3643 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3643
  have eq3652 : y = (M.op x x) := by
    first
    | exact superpose eq3291 eq3651
    | exact resolve eq3651 eq3291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3651
  have eq3653 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq3652
       have i₂ := eq275 x X0
       grind)
    | (have i₁ := eq3652
       have i₂ := eq275 X0 x
       grind)
    | exact superpose eq275 eq3652
    | exact resolve eq3652 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq3690 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | exact superpose eq3291 eq466
    | exact resolve eq466 eq3291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466 eq3291
  have eq3691 : ∀ X0 : G, y = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq3690 X0
       have i₂ := eq3652
       grind)
    | exact superpose eq3652 eq3690
    | exact resolve eq3690 eq3652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3652 eq3690
  have eq3825 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq3691 X0
       have i₂ := eq3653 y
       grind)
    | exact superpose eq3653 eq3691
    | exact resolve eq3691 eq3653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3653 eq3691
  have eq3836 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq3825 y
       grind)
    | exact superpose eq3825 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq3825 y
       grind)
    | exact resolve eq13 eq3825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3864 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq3836 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3836
  have eq3875 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq3864 X0
       have i₂ := eq3825 X0
       grind)
    | exact superpose eq3825 eq3864
    | exact resolve eq3864 eq3825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3825 eq3864
  have eq3899 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 y
       have i₂ := eq3875 (τ X0)
       grind)
    | exact superpose eq3875 eq34
    | exact resolve eq34 eq3875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq3875
  have eq3904 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3899 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3899
    | (have j0 := eq3899 X0
       grind)
    | exact resolve eq3899 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3899
  have eq3908 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq3308 eq3904
    | exact resolve eq3904 eq3308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3308 eq3904
  have eq3921 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq3908 eq95
    | (have j0 := eq95 X0 (σ (M.op x y))
       grind)
    | exact resolve eq95 eq3908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq3908
  have eq3923 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq3921 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3921
  have eq3980 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3923 eq3309
    | exact resolve eq3309 eq3923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3309 eq3923
  have eq3983 : False := by grind
  exact eq3983

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_y_pxy_Equation3273 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq50 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
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
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
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
  have eq58 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
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
  have eq67 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq50 eq16
    | exact resolve eq16 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
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
  have eq72 : x ≠ (M.op x y) ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq81
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq81
    | exact resolve eq81 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq87
    | exact resolve eq87 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq89
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq89
    | exact resolve eq89 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq121 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq121 eq16
    | exact resolve eq16 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq58 x X0
       have i₂ := eq58 x X1
       grind)
    | exact superpose eq58 eq58
    | exact resolve eq58 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq271 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq52
       have i₂ := eq238 x X0
       grind)
    | (have i₁ := eq52
       have i₂ := eq238 X0 x
       grind)
    | exact superpose eq238 eq52
    | exact resolve eq52 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1898 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq90 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1899 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1898
    | exact resolve eq1898 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1898
  have eq1902 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1899
       have r₂ := eq28
       grind)
    | exact resolve eq1899 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1899
  have eq1904 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1902
    | exact resolve eq1902 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1902
  have eq1908 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1904 eq73
    | (have r₁ := eq73
       have r₂ := eq1904
       grind)
    | exact resolve eq73 eq1904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq1904
  have eq1912 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1908
  have eq1913 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1912
  have eq2053 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1913 eq90
    | exact resolve eq90 eq1913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1913
  have eq2057 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2053
  have eq2091 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2057 eq30
    | exact resolve eq30 eq2057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057
  have eq2110 : x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq2091
    | exact resolve eq2091 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2091
  have eq2111 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2110
  have eq2274 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2111 eq27
    | exact resolve eq27 eq2111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2275 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2111 eq30
    | exact resolve eq30 eq2111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2279 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2111 eq90
    | exact resolve eq90 eq2111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq2111
  have eq2288 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2279
  have eq2297 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq2275
    | exact resolve eq2275 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275
  have eq2302 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 y)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2297 eq54
    | exact resolve eq54 eq2297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq2343 : (τ (σ (M.op x y))) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2288 eq67
    | exact resolve eq67 eq2288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq2288
  have eq2345 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq2343
    | exact resolve eq2343 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2343
  have eq2346 : y = (k x y) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2297 eq2345
    | exact resolve eq2345 eq2297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2345
  have eq2352 : y = (k x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2346
  have eq2354 : y = (k x y) ∨ x = y := by
    first
    | (have r₁ := eq2352
       have r₂ := eq72
       grind)
    | exact resolve eq2352 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq2352
  have eq2356 : (σ y) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq2354
       grind)
    | exact superpose eq2354 eq49
    | exact resolve eq49 eq2354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2354
  have eq2361 : (σ y) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2356
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2356
    | exact resolve eq2356 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2356
  have eq3633 : (M.op x x) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2302 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2302
    | (have j0 := eq2302 x
       grind)
    | exact resolve eq2302 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2302
  have eq3750 : (M.op x y) = (M.op x x) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2297 eq3633
    | exact resolve eq3633 eq2297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2297 eq3633
  have eq3768 : (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq3750
  have eq3770 : (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3768
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3768
    | exact resolve eq3768 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3768
  have eq3771 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3770
       have i₂ := eq238 x X0
       grind)
    | (have i₁ := eq3770
       have i₂ := eq238 X0 x
       grind)
    | exact superpose eq238 eq3770
    | exact resolve eq3770 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3780 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq271 x
       have i₂ := eq3770
       grind)
    | exact superpose eq3770 eq271
    | exact resolve eq271 eq3770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3770
  have eq3797 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq3780
    | exact resolve eq3780 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3780
  have eq3865 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op x x) x x
       have i₂ := eq3771 (M.op x x)
       grind)
    | exact superpose eq3771 eq14
    | exact resolve eq14 eq3771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3945 : (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq3797 eq3771
    | exact resolve eq3771 eq3797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3771 eq3797
  have eq3955 : (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq3945
  have eq3971 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq3955 eq2274
    | exact resolve eq2274 eq3955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274
  have eq3988 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3971
  have eq5032 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq3988 eq3865
    | exact resolve eq3865 eq3988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3865 eq3988
  have eq5044 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq5032
  have eq5057 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq5044 eq28
    | exact resolve eq28 eq5044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5044
  have eq5072 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq5057
       have r₂ := eq3955
       grind)
    | exact resolve eq5057 eq3955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3955 eq5057
  have eq5074 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq5072 eq21
    | exact resolve eq21 eq5072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5080 : (σ (k x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq5072 eq121
    | exact resolve eq121 eq5072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq5099 : (k (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq5080
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq5080
    | exact resolve eq5080 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5080
  have eq5103 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq5074
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5074
    | exact resolve eq5074 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5074
  have eq5106 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq5103 eq27
    | exact resolve eq27 eq5103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5108 : ∀ X0 : G, (σ (k x X0)) = (k (σ (M.op x y)) (σ X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq5103 eq36
    | exact resolve eq36 eq5103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq5126 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq5103 eq2361
    | exact resolve eq2361 eq5103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2361
  have eq5137 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by grind
  clear eq5126
  have eq5153 : ∀ X0 : G, (σ (k x X0)) = (σ (k (M.op x y) X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq38 eq5108
    | exact resolve eq5108 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq5108
  have eq5196 : (τ (σ y)) = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq5137 eq146
    | exact resolve eq146 eq5137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5211 : y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq30 eq5196
    | exact resolve eq5196 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5196
  have eq5256 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5099 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq5099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5099
  have eq5273 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq5256
    | exact resolve eq5256 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5256
  have eq5276 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq5273
    | exact resolve eq5273 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5273
  have eq31422 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5276 eq146
    | exact resolve eq146 eq5276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5276
  have eq304265 : (σ (k x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq31422 eq5153
    | exact resolve eq5153 eq31422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5153 eq31422
  have eq304315 : (σ (k x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq304265
  have eq304397 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq304315
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq304315
    | exact resolve eq304315 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304315
  have eq304438 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq304397
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq304397
    | exact resolve eq304397 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq304397
  have eq304697 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5103 eq304438
    | exact resolve eq304438 eq5103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5103 eq304438
  have eq304935 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq304697
  have eq304938 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq304935
       have r₂ := eq28
       grind)
    | exact resolve eq304935 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304935
  have eq304951 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq304938 eq146
    | exact resolve eq146 eq304938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq304954 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq304938 eq5137
    | exact resolve eq5137 eq304938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304938
  have eq305129 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq304954
  have eq305146 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (σ y))) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq305129 eq55
    | exact resolve eq55 eq305129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq305523 : y = (τ (M.op (σ x) (σ y))) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq304951 eq5211
    | exact resolve eq5211 eq304951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5211 eq304951
  have eq305673 : y = (τ (M.op (σ x) (σ y))) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq305523
  have eq2448692 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq305146
    | (have j0 := eq305146 (σ x)
       grind)
    | exact resolve eq305146 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305146
  have eq2450794 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq305129 eq2448692
    | exact resolve eq2448692 eq305129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2448692
  have eq2450949 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2450794
  have eq2450967 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq2450949
    | exact resolve eq2450949 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2450949
  have eq2450974 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq2450967
       have i₂ := eq238 sF2 x
       grind)
    | (have i₁ := eq2450967
       have i₂ := eq238 X0 sF2
       grind)
    | exact superpose eq238 eq2450967
    | exact resolve eq2450967 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq2451079 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) (σ y))) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2450967 eq271
    | exact resolve eq271 eq2450967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq2450967
  have eq2451567 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2451079 eq16
    | exact resolve eq16 eq2451079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2451079
  have eq2452142 : (σ y) = (τ (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq305129 eq2451567
    | exact resolve eq2451567 eq305129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2452157 : y = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2451567 eq305673
    | exact resolve eq305673 eq2451567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305673 eq2451567
  have eq2452717 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op (σ x) (σ y)) := by grind
  clear eq2452157
  have eq2452732 : (σ y) = (τ (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2452142
  have eq2452737 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (σ y) := by
    first
    | exact superpose eq30 eq2452732
    | exact resolve eq2452732 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2452732
  have eq2452787 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y ∨ y = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2452717 eq5106
    | exact resolve eq5106 eq2452717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2452788 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y ∨ y = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2452717 eq5137
    | exact resolve eq5137 eq2452717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2452717
  have eq2453443 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ y = (M.op (σ x) (σ y)) := by grind
  clear eq2452788
  have eq2453444 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ y = (M.op (σ x) (σ y)) := by grind
  clear eq2452787
  have eq2453575 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ y = (M.op (σ x) (σ y)) := by grind
  clear eq2453443
  have eq2453691 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y ∨ y = (σ y) := by
    first
    | exact superpose eq2452737 eq5106
    | exact resolve eq5106 eq2452737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5106
  have eq2453692 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y ∨ y = (σ y) := by
    first
    | exact superpose eq2452737 eq5137
    | exact resolve eq5137 eq2452737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5137 eq2452737
  have eq2454348 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ y = (σ y) := by grind
  clear eq2453692
  have eq2454349 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ y = (σ y) := by grind
  clear eq2453691
  have eq2454479 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ y = (σ y) := by grind
  clear eq2454348
  have eq2461166 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op X1 (M.op (σ x) (σ y))) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    intro X1
    first
    | (have i₁ := eq57 x (M.op x x) x
       have i₂ := eq2450974 (M.op x x)
       grind)
    | exact superpose eq2450974 eq57
    | exact resolve eq57 eq2450974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq2450974
  have eq2463053 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq305129 eq2461166
    | exact resolve eq2461166 eq305129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305129 eq2461166
  have eq2463619 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq2463053 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2463053
  have eq2468989 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2453575 eq2453444
    | exact resolve eq2453444 eq2453575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2453444 eq2453575
  have eq2469364 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op (σ x) (σ y)) := by grind
  clear eq2468989
  have eq2469538 : y = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq2469364
       have r₂ := eq28
       grind)
    | exact resolve eq2469364 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2469364
  have eq2469621 : y ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2469538 eq28
    | exact resolve eq28 eq2469538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2469538
  have eq2471312 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (σ y) ∨ x = y ∨ y = (σ y) := by
    first
    | exact superpose eq2454479 eq2454349
    | exact resolve eq2454349 eq2454479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2454349 eq2454479
  have eq2471687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (σ y) := by grind
  clear eq2471312
  have eq2471863 : y = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2471687
       have r₂ := eq28
       grind)
    | exact resolve eq2471687 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2471687
  have eq2472441 : ∀ X0 : G, y = (M.op X0 y) ∨ x = y ∨ y = (σ (M.op x y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2471863 eq2463619
    | exact resolve eq2463619 eq2471863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2463619 eq2471863
  have eq2472444 : ∀ X0 : G, y = (M.op X0 y) ∨ x = y ∨ y = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq2472441 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2472441
  have eq2472796 : ∀ X0 : G, y = (M.op X0 y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq2472444 X0
       grind)
    | (have r₁ := eq2472444 X0
       have r₂ := eq2469621
       grind)
    | exact resolve eq2472444 eq2469621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2469621 eq2472444
  have eq2475149 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2472796 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2472796
    | (have j0 := eq2472796 x
       grind)
    | exact resolve eq2472796 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2472796
  have eq2475923 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2475149 eq5072
    | exact resolve eq5072 eq2475149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5072 eq2475149
  have eq2477516 : x = y := by grind
  clear eq2475923
  have eq2477790 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq2477516
       grind)
    | exact superpose eq2477516 eq19
    | exact resolve eq19 eq2477516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2477791 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq2477516
       grind)
    | exact superpose eq2477516 eq25
    | exact resolve eq25 eq2477516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2477516
  have eq2478171 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2477791
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2477791
    | exact resolve eq2477791 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2477791
  have eq2478205 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2478171 eq27
    | exact resolve eq27 eq2478171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2478171
  have eq2479263 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2478205 eq71
    | exact resolve eq71 eq2478205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq2478205
  have eq2479663 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2479263
       have i₂ := eq2477790
       grind)
    | exact superpose eq2477790 eq2479263
    | exact resolve eq2479263 eq2477790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2477790 eq2479263
  have eq2480861 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2479663 eq15
    | exact resolve eq15 eq2479663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2479663
  have eq2481585 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq2480861
    | exact resolve eq2480861 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2480861
  have eq2481747 : False := by grind
  exact eq2481747

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_pyy_pxy_Equation3273 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq182 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq180 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq180
    | exact resolve eq180 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq191 : ∀ X0 : G, (k X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq176 X0
       grind)
    | exact superpose eq176 eq174
    | exact resolve eq174 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq182 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq182
    | exact resolve eq182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq182 x X0
       have i₂ := eq182 x X1
       grind)
    | exact superpose eq182 eq182
    | exact resolve eq182 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq263 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq174 X1
       have i₂ := eq220 X1 X0
       grind)
    | (have i₁ := eq174 X1
       have i₂ := eq220 X0 X1
       grind)
    | exact superpose eq220 eq174
    | exact resolve eq174 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq302 : ∀ X0 X1 : G, (k X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq174 X1
       have i₂ := eq263 X1 X0
       grind)
    | exact superpose eq263 eq174
    | exact resolve eq174 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 X1 : G, (k X0 X0) = (M.op x (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X1
       have i₂ := eq263 X1 X0
       grind)
    | exact superpose eq263 eq176
    | exact resolve eq176 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq304 : ∀ X0 X1 : G, (k X0 X0) = (M.op (σ x) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X1
       have i₂ := eq263 X1 X0
       grind)
    | exact superpose eq263 eq177
    | exact resolve eq177 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq313 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq263 X0 (σ X1)
       grind)
    | exact superpose eq263 eq10
    | exact resolve eq10 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq340 : ∀ X0 X1 : G, (k X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq302 (σ X1) X0
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq302 X0 (σ X1)
       grind)
    | exact superpose eq302 eq10
    | exact resolve eq10 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : ∀ X0 X1 : G, (k X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X1 X1)
       have i₂ := eq313 X0 X1
       grind)
    | exact superpose eq313 eq15
    | exact resolve eq15 eq313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq410 : ∀ X0 X1 : G, (k X1 X1) = (τ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq397 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq397
    | exact resolve eq397 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq1095 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = y := by
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
  have eq1099 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1166 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1192 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1166
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq1166
    | exact resolve eq1166 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166
  have eq4031 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1095
       grind)
    | exact superpose eq1095 eq40
    | exact resolve eq40 eq1095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1095
  have eq4032 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4031
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4031
    | exact resolve eq4031 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4031
  have eq4034 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq4032
    | exact resolve eq4032 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4032
  have eq4821 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4034 eq1099
    | exact resolve eq1099 eq4034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099
  have eq4830 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq4821
       have r₂ := eq27
       grind)
    | exact resolve eq4821 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4821
  have eq4834 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4830 eq27
    | exact resolve eq27 eq4830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4839 : ∀ X0 X1 : G, (k X0 X0) = (M.op (σ x) (M.op X1 (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq4830 eq304
    | exact resolve eq304 eq4830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq4840 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4830 eq1192
    | (have r₁ := eq1192
       have r₂ := eq4830
       grind)
    | exact resolve eq1192 eq4830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192
  have eq4841 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq4840
  have eq4842 : (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq4841
  have eq4843 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4034 eq4842
    | exact resolve eq4842 eq4034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4034 eq4842
  have eq4861 : ∀ X0 : G, (σ (M.op x y)) = (k X0 X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4843 eq302
    | exact resolve eq302 eq4843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq4870 : ∀ X0 : G, (τ (σ (M.op x y))) = (k X0 X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4843 eq410
    | exact resolve eq410 eq4843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq4843
  have eq4884 : ∀ X0 : G, (M.op x y) = (k X0 X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq28 eq4870
    | exact resolve eq4870 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4870
  have eq4997 : ∀ X0 : G, (σ (M.op x y)) = (σ (k X0 X0)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq4861 (σ X0)
       grind)
    | exact superpose eq4861 eq10
    | exact resolve eq10 eq4861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5024 : (σ (M.op x y)) = (σ (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4861 eq4997
    | exact resolve eq4997 eq4861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4861 eq4997
  have eq5100 : (σ (M.op x y)) = (τ (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq5024 eq15
    | exact resolve eq15 eq5024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5024
  have eq5118 : (σ x) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq5100
    | exact resolve eq5100 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq5100
  have eq5124 : y = (τ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq5118 eq31
    | exact resolve eq31 eq5118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5118
  have eq5144 : x = y ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq5124
    | exact resolve eq5124 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5124
  have eq5145 : (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq5144
  have eq5158 : (M.op x y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq5145 eq4834
    | exact resolve eq4834 eq5145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4834 eq5145
  have eq5163 : (M.op x y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq5158
  have eq9251 : ∀ X0 : G, (k X0 X0) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq26 eq4839
    | (have j0 := eq4839 X0 (σ x)
       grind)
    | exact resolve eq4839 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4839
  have eq9413 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4830 eq9251
    | exact resolve eq9251 eq4830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9251
  have eq9491 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq26 eq9413
    | (have j0 := eq9413 X0
       grind)
    | exact resolve eq9413 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9413
  have eq9553 : ∀ X0 : G, (σ y) = (k X0 X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4830 eq9491
    | exact resolve eq9491 eq4830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4830 eq9491
  have eq9592 : (M.op x y) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4884 eq9553
    | exact resolve eq9553 eq4884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4884 eq9553
  have eq9615 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq9592
       have r₂ := eq5163
       grind)
    | exact resolve eq9592 eq5163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5163 eq9592
  have eq9626 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq9615 eq31
    | exact resolve eq31 eq9615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq9615
  have eq9647 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq9626
    | exact resolve eq9626 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq9626
  have eq9648 : y = (M.op x y) ∨ x = y := by grind
  clear eq9647
  have eq9651 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq9648
       grind)
    | exact superpose eq9648 eq18
    | exact resolve eq18 eq9648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9652 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq9648
       grind)
    | exact superpose eq9648 eq24
    | exact resolve eq24 eq9648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9648
  have eq9661 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq9652
    | exact resolve eq9652 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9652
  have eq9712 : ∀ X0 : G, (k X0 X0) = (M.op x (M.op x y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq9651 eq303
    | exact resolve eq303 eq9651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq9714 : (k x x) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq9651 eq191
    | exact resolve eq191 eq9651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq9726 : (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq9651 eq9714
    | exact resolve eq9714 eq9651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9714
  have eq9728 : ∀ X0 : G, (M.op x y) = (k X0 X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq9651 eq9712
    | exact resolve eq9712 eq9651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9651 eq9712
  have eq9745 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq219 x X0
       have i₂ := eq9726
       grind)
    | exact superpose eq9726 eq219
    | exact resolve eq219 eq9726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq9754 : ∀ X0 : G, (σ (M.op x y)) = (k X0 X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq340 X0 x
       have i₂ := eq9726
       grind)
    | exact superpose eq9726 eq340
    | exact resolve eq340 eq9726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340 eq9726
  have eq9800 : ∀ X0 : G, (σ (M.op x y)) = (k X0 X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq20 eq9754
    | (have j0 := eq9754 X0
       grind)
    | exact resolve eq9754 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9754
  have eq9804 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq20 eq9745
    | (have j0 := eq9745 X0
       grind)
    | exact resolve eq9745 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9745
  have eq9822 : ∀ X0 : G, (σ y) = (k X0 X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq9661 eq9800
    | exact resolve eq9800 eq9661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9800
  have eq9825 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9804 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9804
    | (have j0 := eq9804 X0
       grind)
    | exact resolve eq9804 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9804
  have eq9840 : (M.op x y) = (σ y) ∨ x = y := by
    first
    | exact superpose eq9728 eq9822
    | exact resolve eq9822 eq9728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9822
  have eq9842 : ∀ X0 : G, (k X0 X0) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9825 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq9825
    | exact resolve eq9825 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9825
  have eq9853 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq9661 eq9842
    | exact resolve eq9842 eq9661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9842
  have eq9857 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq26 eq9853
    | (have j0 := eq9853 X0
       grind)
    | exact resolve eq9853 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9853
  have eq9859 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq9728 eq9857
    | exact resolve eq9857 eq9728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9728 eq9857
  have eq9921 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq9859 eq27
    | exact resolve eq27 eq9859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9859
  have eq9944 : (M.op x y) ≠ (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq9661 eq9921
    | exact resolve eq9921 eq9661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9661 eq9921
  have eq9948 : (M.op x y) ≠ (σ y) ∨ x = y := by grind
  clear eq9944
  have eq9949 : x = y := by
    first
    | (have r₁ := eq9948
       have r₂ := eq9840
       grind)
    | exact resolve eq9948 eq9840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9840 eq9948
  have eq10278 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq9949
       grind)
    | exact superpose eq9949 eq18
    | exact resolve eq18 eq9949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq10279 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq9949
       grind)
    | exact superpose eq9949 eq24
    | exact resolve eq24 eq9949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq9949
  have eq10284 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq10279
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10279
    | exact resolve eq10279 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10279
  have eq10285 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq10278
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq10278
    | exact resolve eq10278 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10278
  have eq10287 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10284 eq26
    | exact resolve eq26 eq10284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq10284
  have eq10309 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq10287
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq10287
    | exact resolve eq10287 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq10287
  have eq10316 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq10285
       grind)
    | exact superpose eq10285 eq39
    | exact resolve eq39 eq10285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq10285
  have eq10370 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq10316
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10316
    | exact resolve eq10316 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq10316
  have eq10383 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10309 eq10370
    | exact resolve eq10370 eq10309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10309 eq10370
  have eq10390 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq10383
    | exact resolve eq10383 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq10383
  have eq10392 : False := by grind
  exact eq10392

/-- `Equation3292`: `x ◇ x = y ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation3292 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3292 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3292.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
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
  clear eq22
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
  have eq50 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op X3 (M.op X4 (M.op X3 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X2 X3 X4
       have i₂ := eq14 X2 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 (M.op x y))) := by
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
  have eq52 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq95 x y
       grind)
    | exact superpose eq95 eq44
    | (have j1 := eq95 x y
       grind)
    | exact resolve eq44 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq120 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq118
    | exact resolve eq118 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq120
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq120
    | exact resolve eq120 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq121 eq95
    | (have j0 := eq95 (σ x) (σ y)
       grind)
    | exact resolve eq95 eq121
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
  have eq224 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq130 eq52
    | exact resolve eq52 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq228 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq224
    | (have j0 := eq224 (σ x)
       grind)
    | exact resolve eq224 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq224 eq14
    | exact resolve eq14 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq261 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq228 eq229
    | exact resolve eq229 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228 eq229
  have eq268 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq261 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq269 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq130 eq268
    | exact resolve eq268 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq278 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq269 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq280 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq278
    | (have j0 := eq278 X0
       grind)
    | exact resolve eq278 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq281 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq130 eq280
    | exact resolve eq280 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq280
  have eq290 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq281 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq321 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq290 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq290 (σ y)
       grind)
    | exact resolve eq13 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq330 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq321 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq429 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq330 eq121
    | exact resolve eq121 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq330
  have eq433 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq429
  have eq436 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq433
    | exact resolve eq433 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq438 : y = (M.op x y) := by
    first
    | (have r₁ := eq436
       have r₂ := eq27
       grind)
    | exact resolve eq436 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq442 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq438 eq20
    | exact resolve eq20 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq444 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq438 eq51
    | exact resolve eq51 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq456 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq442
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq442
    | exact resolve eq442 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq457 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq456 eq26
    | exact resolve eq26 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq544 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op x y)))) = (M.op X2 (M.op y y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq50
    | exact resolve eq50 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq51
  have eq564 : ∀ X2 : G, (M.op (M.op x y) (M.op x y)) = (M.op X2 (M.op y y)) := by
    intro X2
    first
    | (have i₁ := eq544 x X2 X2
       have i₂ := eq14 sF0 x X2
       grind)
    | exact superpose eq14 eq544
    | exact resolve eq544 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq576 : ∀ X2 : G, (M.op y y) = (M.op X2 (M.op y y)) := by
    intro X2
    first
    | exact superpose eq438 eq564
    | exact resolve eq564 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq769 : ∀ X0 : G, (M.op y y) ≠ (M.op y y) ∨ (M.op X0 (M.op y y)) = (k X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op y y)
       have i₂ := eq576 (M.op y y)
       grind)
    | exact superpose eq576 eq13
    | (have j0 := eq13 X0 (M.op y y)
       grind)
    | (have r₁ := eq13 X0 (M.op y y)
       have r₂ := eq576 (M.op y y)
       grind)
    | exact resolve eq13 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq779 : ∀ X0 : G, (M.op X0 (M.op y y)) = (k X0 (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq769 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq786 : ∀ X0 : G, (M.op y y) = (k X0 (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq779 X0
       have i₂ := eq576 X0
       grind)
    | exact superpose eq576 eq779
    | exact resolve eq779 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq779
  have eq1036 : (M.op y y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq444 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq444
    | (have j0 := eq444 x
       grind)
    | exact resolve eq444 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq1063 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq438 eq1036
    | exact resolve eq1036 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq1070 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1063
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1063
    | exact resolve eq1063 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1063
  have eq1072 : y = (M.op y y) := by
    first
    | exact superpose eq438 eq1070
    | exact resolve eq1070 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438 eq1070
  have eq1073 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq786 X0
       have i₂ := eq1072
       grind)
    | exact superpose eq1072 eq786
    | exact resolve eq786 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786 eq1072
  have eq1276 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 y
       have i₂ := eq1073 (τ X0)
       grind)
    | exact superpose eq1073 eq34
    | exact resolve eq34 eq1073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1073
  have eq1281 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1276 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1276
    | (have j0 := eq1276 X0
       grind)
    | exact resolve eq1276 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1276
  have eq1285 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq456 eq1281
    | exact resolve eq1281 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456 eq1281
  have eq1445 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1285 eq95
    | (have j0 := eq95 X0 (σ (M.op x y))
       grind)
    | exact resolve eq95 eq1285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq1285
  have eq1447 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq1445 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445
  have eq1546 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1447 eq457
    | exact resolve eq457 eq1447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457 eq1447
  have eq1549 : False := by grind
  exact eq1549

/-- `Equation3292`: `x ◇ x = y ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyy_x_pxy_Equation3292 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3292 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3292.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq179 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X1 X0) X2 X1
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ X2 ∨ (M.op X0 (M.op X1 (M.op X0 X2))) = (k X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq627 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 (M.op X2 X1)
       have i₂ := eq179 X1 X2 X0
       grind)
    | (have i₁ := eq16 X0 X0 X2
       have i₂ := eq179 X0 X1 X2
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq844 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X0 (M.op X1 X1))
       have i₂ := eq627 X0 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq627 eq13
    | exact resolve eq13 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq934 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (k X2 X2) ∨ (M.op X0 (M.op X1 (M.op X0 X2))) = X2 ∨ (M.op X0 (M.op X1 (M.op X0 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq11
    | exact resolve eq11 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq936 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X1 (M.op X2 (M.op X0 X0))) ∨ (M.op X0 X0) = (M.op X2 (M.op X0 X0)) ∨ (M.op X2 (M.op X0 X0)) = (M.op (M.op X2 (M.op X0 X0)) (M.op X2 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq627 X0 X1 X2
       grind)
    | exact superpose eq627 eq11
    | (have j0 := eq11 (M.op X2 (M.op X0 X0)) (M.op X2 (M.op X0 X0))
       grind)
    | exact resolve eq11 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq951 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq954 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1034 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (k X2 X2) ∨ (M.op X0 (M.op X1 (M.op X0 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq934 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq1075 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X1 (M.op X2 (M.op X0 X0))) ∨ (M.op X2 (M.op X0 X0)) = (M.op (M.op X2 (M.op X0 X0)) (M.op X2 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq936 X0 X1 X2
       have j1 := eq844 X0 X2 X1
       grind)
    | (have r₁ := eq936 X0 X1 X1
       have r₂ := eq844 X0 X1 X2
       grind)
    | (have r₁ := eq936 X0 X1 (M.op X0 X0)
       have r₂ := eq844 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)) X2
       grind)
    | exact resolve eq936 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq1078 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1034 X0 X1 X2
       have j1 := eq181 X0 X1 X2 X2
       grind)
    | (have r₁ := eq1034 X0 X1 X2
       have r₂ := eq181 X0 X1 X2 x
       grind)
    | exact resolve eq1034 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq1034
  have eq1108 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X1 (M.op X2 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1075 X0 X1 X2
       have i₂ := eq627 X2 X0 (M.op X2 (M.op X0 X0))
       grind)
    | exact superpose eq627 eq1075
    | (have j0 := eq1075 X0 X1 X2
       grind)
    | exact resolve eq1075 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq1126 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X1 (M.op X2 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1108 X0 X1 X2
       have j1 := eq844 X0 X2 X1
       grind)
    | (have r₁ := eq1108 X0 X1 X1
       have r₂ := eq844 X0 X1 X2
       grind)
    | exact resolve eq1108 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq1108
  have eq1211 : ∀ X0 : G, (k y y) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1078 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1078
    | (have j0 := eq1078 x X0 y
       grind)
    | exact resolve eq1078 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1214 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq1078
    | (have j0 := eq1078 (σ x) X0 (σ y)
       grind)
    | exact resolve eq1078 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1233 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X1))) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1078 X2 (M.op X2 X1) X1
       have i₂ := eq179 X1 X2 X0
       grind)
    | (have i₁ := eq1078 X0 X2 X0
       have i₂ := eq179 X0 X1 X2
       grind)
    | exact superpose eq179 eq1078
    | exact resolve eq1078 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1252 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq627 x X0 X0
       have i₂ := eq1078 X0 x X0
       grind)
    | exact superpose eq1078 eq627
    | exact resolve eq627 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq1286 : ∀ X0 X1 X2 : G, (k X1 X1) = (M.op X2 (M.op X0 (k X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1233 X0 X1 X2
       have i₂ := eq1252 X1
       grind)
    | exact superpose eq1252 eq1233
    | exact resolve eq1233 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233
  have eq1346 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq1252 X0
       grind)
    | exact superpose eq1252 eq13
    | exact resolve eq13 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1938 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 X1)) = (k X3 (M.op X4 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq1126 (M.op X1 X0) X1 x
       have i₂ := eq179 X0 X1 x
       grind)
    | (have i₁ := eq1126 (M.op X0 X0) X1 x
       have i₂ := eq179 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq179 eq1126
    | exact resolve eq1126 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq1126
  have eq2006 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (k X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1938 X0 X1 X3 x
       have i₂ := eq627 X0 X1 x
       grind)
    | exact superpose eq627 eq1938
    | exact resolve eq1938 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627 eq1938
  have eq2015 : ∀ X0 X1 X3 : G, (M.op X0 (k X1 X1)) = (k X3 (k X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq2006 X0 X0 X3
       have i₂ := eq1252 X0
       grind)
    | exact superpose eq1252 eq2006
    | exact resolve eq2006 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2006
  have eq2721 : ∀ X0 X1 X2 : G, (k X1 X1) = (M.op X2 (k X0 (k X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1286 x X1 X2
       have i₂ := eq2015 x X1 X0
       grind)
    | exact superpose eq2015 eq1286
    | exact resolve eq1286 eq2015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1286 eq2015
  have eq2908 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq951
       grind)
    | exact superpose eq951 eq40
    | exact resolve eq40 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq2909 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2908
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2908
    | exact resolve eq2908 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2908
  have eq2911 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq2909
    | exact resolve eq2909 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2909
  have eq2913 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2911
       have i₂ := eq1252 y
       grind)
    | exact superpose eq1252 eq2911
    | exact resolve eq2911 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2911
  have eq7160 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2913 eq954
    | exact resolve eq954 eq2913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954 eq2913
  have eq7169 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq7160
       have r₂ := eq27
       grind)
    | exact resolve eq7160 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7160
  have eq7174 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7169
       have i₂ := eq1252 sF3
       grind)
    | exact superpose eq1252 eq7169
    | exact resolve eq7169 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252 eq7169
  have eq7188 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7174 eq152
    | exact resolve eq152 eq7174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7174
  have eq7207 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq7188
    | exact resolve eq7188 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7188
  have eq7208 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq7207
  have eq7229 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq7208
       grind)
    | exact superpose eq7208 eq40
    | exact resolve eq40 eq7208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq7234 : ∀ X0 : G, y ≠ y ∨ y = (k X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1346 y x
       have i₂ := eq7208
       grind)
    | exact superpose eq7208 eq1346
    | (have r₁ := eq1346 y x
       have r₂ := eq7208
       grind)
    | exact resolve eq1346 eq7208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7208
  have eq7243 : ∀ X0 : G, y = (k X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq7234 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7234
  have eq7248 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7229
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7229
    | exact resolve eq7229 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7229
  have eq7266 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq34 X0 y
       have i₂ := eq7243 (τ X0)
       grind)
    | exact superpose eq7243 eq34
    | exact resolve eq34 eq7243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7243
  have eq7291 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7266 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7266
    | (have j0 := eq7266 X0
       grind)
    | exact resolve eq7266 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7266
  have eq7320 : ∀ X0 X1 : G, (σ y) = (M.op X0 (k X1 (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq7248 eq2721
    | exact resolve eq2721 eq7248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7248
  have eq7327 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7291 eq7320
    | exact resolve eq7320 eq7291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7291 eq7320
  have eq8135 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7327 eq26
    | (have j1 := eq7327 (σ x)
       grind)
    | exact resolve eq26 eq7327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7327
  have eq8146 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq8135
  have eq8179 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (σ x) (M.op X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8146 eq1214
    | exact resolve eq1214 eq8146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq9198 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq8179
    | (have j0 := eq8179 (σ x)
       grind)
    | exact resolve eq8179 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8179
  have eq9264 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8146 eq9198
    | exact resolve eq9198 eq8146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9198
  have eq9297 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq9264
    | exact resolve eq9264 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9264
  have eq9325 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8146 eq9297
    | exact resolve eq9297 eq8146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8146 eq9297
  have eq9375 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9325 eq152
    | exact resolve eq152 eq9325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq9380 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9325 eq1346
    | (have r₁ := eq1346 (σ y) x
       have r₂ := eq9325
       grind)
    | exact resolve eq1346 eq9325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9325
  have eq9389 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq9380 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9380
  have eq9394 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq9375
    | exact resolve eq9375 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9375
  have eq9437 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9389 eq380
    | exact resolve eq380 eq9389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq9389
  have eq9483 : ∀ X0 : G, y = (k X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq31 eq9437
    | exact resolve eq9437 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq9437
  have eq9525 : ∀ X0 X1 : G, y = (M.op X0 (k X1 y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq2721 X0 y x
       have i₂ := eq9394
       grind)
    | exact superpose eq9394 eq2721
    | exact resolve eq2721 eq9394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9394
  have eq9534 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9483 eq9525
    | exact resolve eq9525 eq9483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9483 eq9525
  have eq9739 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq9534 x
       grind)
    | exact superpose eq9534 eq18
    | (have j1 := eq9534 x
       grind)
    | exact resolve eq18 eq9534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9534
  have eq9750 : y = (M.op x y) := by grind
  clear eq9739
  have eq9764 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq9750
       grind)
    | exact superpose eq9750 eq18
    | exact resolve eq18 eq9750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq9765 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq9750
       grind)
    | exact superpose eq9750 eq24
    | exact resolve eq24 eq9750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq9853 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9765 eq20
    | exact resolve eq20 eq9765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9765
  have eq9941 : (k y y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq9764 eq1211
    | exact resolve eq1211 eq9764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq9970 : (M.op x y) = (k y y) := by
    first
    | exact superpose eq9764 eq9941
    | exact resolve eq9941 eq9764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9764 eq9941
  have eq9978 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq9970
       have i₂ := eq9750
       grind)
    | exact superpose eq9750 eq9970
    | exact resolve eq9970 eq9750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9750 eq9970
  have eq10010 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq9978 eq37
    | exact resolve eq37 eq9978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq10016 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq9978 eq1346
    | (have r₁ := eq1346 (M.op x y) x
       have r₂ := eq9978
       grind)
    | exact resolve eq1346 eq9978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346 eq9978
  have eq10025 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq10016 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10016
  have eq10035 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq10010
    | exact resolve eq10010 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10010
  have eq10046 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq9853 eq10035
    | exact resolve eq10035 eq9853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10035
  have eq10069 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq10025 eq34
    | exact resolve eq34 eq10025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq10025
  have eq10104 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10069
    | (have j0 := eq10069 X0
       grind)
    | exact resolve eq10069 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq10069
  have eq10118 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq9853 eq10104
    | exact resolve eq10104 eq9853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10104
  have eq10144 : ∀ X0 X1 : G, (σ y) = (M.op X0 (k X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq10046 eq2721
    | exact resolve eq2721 eq10046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2721 eq10046
  have eq10151 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq10118 eq10144
    | exact resolve eq10144 eq10118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10118 eq10144
  have eq11350 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10151 eq26
    | (have j1 := eq10151 (σ x)
       grind)
    | exact resolve eq26 eq10151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq10151
  have eq11434 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq11350 eq27
    | exact resolve eq27 eq11350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq11350
  have eq11481 : False := by grind
  exact eq11481

/-- `Equation3292`: `x ◇ x = y ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then Y else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_y_pyy_pxy_Equation3292 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3292 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3292.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
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
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq175 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X1 X0) X2 X1
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X1 X1)) (M.op X2 (M.op X1 X1))) = (M.op X3 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq179 (M.op X1 X1) X2 X3
       have i₂ := eq179 X1 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq179 (M.op X1 X0) X1 X2
       have i₂ := eq179 X0 X1 X2
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq627 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 (M.op X2 X1)
       have i₂ := eq179 X1 X2 X0
       grind)
    | (have i₁ := eq16 X0 X0 X2
       have i₂ := eq179 X0 X1 X2
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq657 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op X3 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq609 X0 X1 x X3
       have i₂ := eq627 x X1 (M.op x (M.op X1 X1))
       grind)
    | exact superpose eq627 eq609
    | exact resolve eq609 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609 eq627
  have eq912 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq915 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq966 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq967 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq966 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966
  have eq1173 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq912
       grind)
    | exact superpose eq912 eq40
    | exact resolve eq40 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq912
  have eq1174 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1173
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1173
    | exact resolve eq1173 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1173
  have eq1176 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1174
    | exact resolve eq1174 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174
  have eq1351 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1176 eq915
    | exact resolve eq915 eq1176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq1358 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1351
       have r₂ := eq27
       grind)
    | exact resolve eq1351 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351
  have eq1368 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1358 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1358
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq1358
       grind)
    | exact resolve eq13 eq1358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358
  have eq1373 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq1368 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368
  have eq1398 : (τ (σ y)) = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1373 eq107
    | exact resolve eq107 eq1373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq1373
  have eq1405 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq1398
    | exact resolve eq1398 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1398
  have eq1415 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq1405
       have r₂ := eq13 x y
       grind)
    | exact resolve eq1405 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405
  have eq1427 : y ≠ y ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq967 y
       have i₂ := eq1415
       grind)
    | exact superpose eq1415 eq967
    | (have j0 := eq967 y
       grind)
    | (have r₁ := eq967 y
       have r₂ := eq1415
       grind)
    | exact resolve eq967 eq1415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415
  have eq1428 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1427
  have eq1477 : ∀ X0 : G, (M.op y y) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq179 y y x
       have i₂ := eq1428
       grind)
    | exact superpose eq1428 eq179
    | exact resolve eq179 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1481 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1428 eq1477
    | exact resolve eq1477 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428 eq1477
  have eq1563 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1481 x
       grind)
    | exact superpose eq1481 eq18
    | (have j1 := eq1481 x
       grind)
    | exact resolve eq18 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1481
  have eq1565 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1563
  have eq1569 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1565 eq27
    | exact resolve eq27 eq1565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1570 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1565 eq176
    | exact resolve eq176 eq1565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1612 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1570
    | (have j0 := eq1570 (σ x)
       grind)
    | exact resolve eq1570 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1570
  have eq1645 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1565 eq1612
    | exact resolve eq1612 eq1565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612
  have eq1654 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1645
    | exact resolve eq1645 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645
  have eq1656 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1565 eq1654
    | exact resolve eq1654 eq1565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1565 eq1654
  have eq1668 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1656 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1656
       grind)
    | exact resolve eq13 eq1656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1656
  have eq1673 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1668 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1668
  have eq1697 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1673 eq1176
    | exact resolve eq1176 eq1673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176 eq1673
  have eq1704 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq1697
  have eq1713 : y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1704
       have r₂ := eq1569
       grind)
    | exact resolve eq1704 eq1569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569 eq1704
  have eq2230 : ∀ X0 : G, (M.op y y) = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq179 y y x
       have i₂ := eq1713
       grind)
    | exact superpose eq1713 eq179
    | exact resolve eq179 eq1713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq2238 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1713 eq2230
    | exact resolve eq2230 eq1713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1713 eq2230
  have eq2313 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2238 x
       grind)
    | exact superpose eq2238 eq18
    | (have j1 := eq2238 x
       grind)
    | exact resolve eq18 eq2238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2238
  have eq2315 : y = (M.op x y) := by grind
  clear eq2313
  have eq2319 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2315
       grind)
    | exact superpose eq2315 eq18
    | exact resolve eq18 eq2315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2320 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2315
       grind)
    | exact superpose eq2315 eq24
    | exact resolve eq24 eq2315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2328 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2320 eq20
    | exact resolve eq20 eq2320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2320
  have eq2388 : (M.op y y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq2319 eq175
    | exact resolve eq175 eq2319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq2401 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq2319 eq2388
    | exact resolve eq2388 eq2319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319 eq2388
  have eq2405 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq2401
       have i₂ := eq2315
       grind)
    | exact superpose eq2315 eq2401
    | exact resolve eq2401 eq2315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2315 eq2401
  have eq2420 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2405 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq2405
       grind)
    | exact resolve eq13 eq2405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2405
  have eq2428 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq2420 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2420
  have eq2456 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2428 eq37
    | exact resolve eq37 eq2428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2428
  have eq2463 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq2456
    | exact resolve eq2456 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2456
  have eq2468 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq2328 eq2463
    | exact resolve eq2463 eq2328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2463
  have eq2522 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2468 eq967
    | (have j0 := eq967 (σ y)
       grind)
    | (have r₁ := eq967 (σ y)
       have r₂ := eq2468
       grind)
    | exact resolve eq967 eq2468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967 eq2468
  have eq2523 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq2522
  have eq2602 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq2523 eq657
    | exact resolve eq657 eq2523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq2605 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq2523 eq2602
    | exact resolve eq2602 eq2523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2523 eq2602
  have eq2629 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2605 eq26
    | (have j1 := eq2605 (σ x)
       grind)
    | exact resolve eq26 eq2605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2605
  have eq2641 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq2629 eq27
    | exact resolve eq27 eq2629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2629
  have eq2651 : False := by grind
  exact eq2651

/-- `Equation3296`: `x ◇ x = y ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if X = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pyy_pyy_pxy_Equation3296 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3296 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3296.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X2 X0))) := by
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
  clear eq44
  have eq53 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : y ≠ (M.op x y) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq83 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq87 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq83 sF2
       grind)
    | exact superpose eq83 eq50
    | exact resolve eq50 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq88 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq87
       have i₂ := eq83 x
       grind)
    | exact superpose eq83 eq87
    | exact resolve eq87 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq97 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq81
       have i₂ := eq83 sF3
       grind)
    | exact superpose eq83 eq81
    | exact resolve eq81 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq98 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq97
       have i₂ := eq83 y
       grind)
    | exact superpose eq83 eq97
    | exact resolve eq97 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq97
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
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
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq106
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq106
    | exact resolve eq106 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq111
    | exact resolve eq111 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq113
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq113
    | exact resolve eq113 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq125 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq16
    | exact resolve eq16 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq400 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 y
       have i₂ := eq237 y
       grind)
    | exact superpose eq237 eq14
    | exact resolve eq14 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1562 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1563 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1562
    | exact resolve eq1562 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562
  have eq1566 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1563
       have r₂ := eq28
       grind)
    | exact resolve eq1563 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1563
  have eq1568 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1566
    | exact resolve eq1566 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1566
  have eq1572 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1568 eq70
    | (have r₁ := eq70
       have r₂ := eq1568
       grind)
    | exact resolve eq70 eq1568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq1573 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1568 eq54
    | exact resolve eq54 eq1568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1575 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1572
  have eq1576 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27 eq1573
    | (have j0 := eq1573 X0
       grind)
    | exact resolve eq1573 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1573
  have eq1857 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1575 eq114
    | exact resolve eq114 eq1575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq1858 : (k x y) = (τ (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1575 eq63
    | exact resolve eq63 eq1575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1575
  have eq1861 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1857
  have eq1865 : (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq125 eq1858
    | exact resolve eq1858 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq1858
  have eq1868 : (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1865
       have r₂ := eq69
       grind)
    | exact resolve eq1865 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq1865
  have eq1871 : (k (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq45
       have i₂ := eq1868
       grind)
    | exact superpose eq1868 eq45
    | exact resolve eq45 eq1868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq1868
  have eq1876 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1871
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq1871
    | exact resolve eq1871 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1871
  have eq1884 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1876 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq1876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1876
  have eq1885 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq1884
  have eq1889 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq1885
    | exact resolve eq1885 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885
  have eq1892 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1889
    | exact resolve eq1889 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1889
  have eq2295 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1576 eq1861
    | exact resolve eq1861 eq1576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1576 eq1861
  have eq2326 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq2295 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2295
  have eq2354 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1568 eq2326
    | exact resolve eq2326 eq1568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1568 eq2326
  have eq2375 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq2354 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2354
  have eq2401 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2375 eq27
    | (have j1 := eq2375 (σ x)
       grind)
    | exact resolve eq27 eq2375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2375
  have eq2415 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2401
       have r₂ := eq28
       grind)
    | exact resolve eq2401 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2401
  have eq2421 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq2415 eq30
    | exact resolve eq30 eq2415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2415
  have eq2441 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq2421
    | exact resolve eq2421 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2421
  have eq2442 : y = (M.op x y) ∨ x = y := by grind
  clear eq2441
  have eq2592 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2442 eq21
    | exact resolve eq21 eq2442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2594 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2442 eq53
    | exact resolve eq53 eq2442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq2602 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op y y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2442 eq400
    | exact resolve eq400 eq2442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq2606 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq2602 x
       have i₂ := eq237 x
       grind)
    | exact superpose eq237 eq2602
    | exact resolve eq2602 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq2602
  have eq2613 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2594 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2594
    | (have j0 := eq2594 X0
       grind)
    | exact resolve eq2594 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2594
  have eq2615 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2592
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2592
    | exact resolve eq2592 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2592
  have eq2801 : ∀ X0 : G, (M.op y y) = (M.op X0 y) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq2442 eq2613
    | exact resolve eq2613 eq2442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2442
  have eq2840 : ∀ X0 : G, (M.op y y) = (M.op X0 y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq2801 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2801
  have eq3080 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op X0 y) ∨ x = y ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq2613 X1
       have i₂ := eq2840 X0
       grind)
    | (have i₁ := eq2613 X0
       have i₂ := eq2840 y
       grind)
    | exact superpose eq2840 eq2613
    | exact resolve eq2613 eq2840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2613 eq2840
  have eq3109 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op X0 y) ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq3080 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3080
  have eq3551 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq3109 x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3109
    | (have j0 := eq3109 x X0
       grind)
    | exact resolve eq3109 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3109
  have eq3714 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq3551 eq2606
    | exact resolve eq2606 eq3551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2606 eq3551
  have eq3717 : (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq3714
  have eq3740 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq98
       have i₂ := eq3717
       grind)
    | exact superpose eq3717 eq98
    | exact resolve eq98 eq3717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq3717
  have eq3774 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq3740
    | exact resolve eq3740 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3740
  have eq4174 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq3774 eq1892
    | exact resolve eq1892 eq3774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1892 eq3774
  have eq4190 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq4174
  have eq4204 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq4190
       have r₂ := eq28
       grind)
    | exact resolve eq4190 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4190
  have eq4826 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq4204 eq28
    | exact resolve eq28 eq4204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4204
  have eq4838 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq4826
       have r₂ := eq2615
       grind)
    | exact resolve eq4826 eq2615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2615 eq4826
  have eq4842 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq4838 eq30
    | exact resolve eq30 eq4838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4838
  have eq4888 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq4842
    | exact resolve eq4842 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4842
  have eq4889 : x = y := by grind
  clear eq4888
  have eq5326 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq4889
       grind)
    | exact superpose eq4889 eq19
    | exact resolve eq19 eq4889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq5327 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq4889
       grind)
    | exact superpose eq4889 eq25
    | exact resolve eq25 eq4889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq4889
  have eq5353 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq5327
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5327
    | exact resolve eq5327 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq5327
  have eq5357 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5353 eq27
    | exact resolve eq27 eq5353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq5353
  have eq5803 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5357 eq88
    | exact resolve eq88 eq5357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq5357
  have eq5832 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq5803
       have i₂ := eq5326
       grind)
    | exact superpose eq5326 eq5803
    | exact resolve eq5803 eq5326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5326 eq5803
  have eq5846 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5832 eq15
    | exact resolve eq15 eq5832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5832
  have eq5889 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq5846
    | exact resolve eq5846 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq5846
  have eq5898 : False := by grind
  exact eq5898
