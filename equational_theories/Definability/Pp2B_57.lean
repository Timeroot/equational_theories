import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3690`: `x ◇ x = (y ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyx_x_pyx_x_pyx_Equation3690 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3690 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3690.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
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
  have eq86 : y ≠ (M.op x y) ∨ (M.op x x) = (M.op y x) ∨ y = (k y x) := by
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
  have eq87 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  clear eq22 eq36
  have eq124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq94 y x
       grind)
    | exact superpose eq94 eq100
    | (have j1 := eq94 y x
       grind)
    | exact resolve eq100 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq124
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq124
    | exact resolve eq124 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq134 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq132
    | exact resolve eq132 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq135 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq134
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq134
    | exact resolve eq134 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq204 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq135 eq94
    | (have j0 := eq94 (σ y) (σ x)
       grind)
    | exact resolve eq94 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq204
    | exact resolve eq204 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq208 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq205
       have r₂ := eq27
       grind)
    | exact resolve eq205 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq210 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq208
    | exact resolve eq208 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq212 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq210 eq27
    | exact resolve eq27 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2434 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq210 eq87
    | (have r₁ := eq87
       have r₂ := eq210
       grind)
    | exact resolve eq87 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq210
  have eq2435 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq2434
  have eq2437 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2435 eq13
    | (have j0 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2435
       grind)
    | exact resolve eq13 eq2435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2435
  have eq2480 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq2437
  have eq2481 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2480
    | exact resolve eq2480 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2480
  have eq2484 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq135 eq2481
    | exact resolve eq2481 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq2481
  have eq2492 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq2484
  have eq2495 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2492
       have r₂ := eq212
       grind)
    | exact resolve eq2492 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq2492
  have eq2496 : y = (M.op x y) := by
    first
    | (have r₁ := eq2495
       have r₂ := eq27
       grind)
    | exact resolve eq2495 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2495
  have eq2497 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2496 eq20
    | exact resolve eq20 eq2496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2500 : y ≠ y ∨ (M.op x x) = (M.op y x) ∨ y = (k y x) := by
    first
    | exact superpose eq2496 eq86
    | (have r₁ := eq86
       have r₂ := eq2496
       grind)
    | exact resolve eq86 eq2496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq2505 : (M.op x x) = (M.op y x) ∨ y = (k y x) := by grind
  clear eq2500
  have eq2511 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2497
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2497
    | exact resolve eq2497 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2497
  have eq2618 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2511 eq26
    | exact resolve eq26 eq2511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq3233 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2505
       grind)
    | exact superpose eq2505 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2505
       grind)
    | exact resolve eq13 eq2505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2505
  have eq3260 : (M.op x y) = (k y x) ∨ y = (k y x) := by grind
  clear eq3233
  have eq3261 : (M.op x y) = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq3260
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3260
    | exact resolve eq3260 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3260
  have eq3263 : y = (k y x) ∨ y = (k y x) := by
    first
    | exact superpose eq2496 eq3261
    | exact resolve eq3261 eq2496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2496 eq3261
  have eq3264 : y = (k y x) := by grind
  clear eq3263
  have eq3269 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq100
       have i₂ := eq3264
       grind)
    | exact superpose eq3264 eq100
    | exact resolve eq100 eq3264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq3264
  have eq3276 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq2511 eq3269
    | exact resolve eq3269 eq2511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3269
  have eq3278 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq3276
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3276
    | exact resolve eq3276 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3276
  have eq3279 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq2511 eq3278
    | exact resolve eq3278 eq2511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2511 eq3278
  have eq3283 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq3279 eq94
    | (have j0 := eq94 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq94 eq3279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq3279
  have eq3284 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq3283
  have eq3286 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2618 eq3284
    | exact resolve eq3284 eq2618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2618 eq3284
  have eq3289 : False := by grind
  exact eq3289

/-- `Equation3690`: `x ◇ x = (y ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_x_pyx_x_pyx_Equation3690 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3690 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3690.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
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
  have eq79 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq22 eq36
  have eq84 : y ≠ (M.op x y) ∨ y = (M.op y x) ∨ y = (k y x) := by
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
  have eq85 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
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
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq101 y x
       grind)
    | exact superpose eq101 eq79
    | (have j1 := eq101 y x
       grind)
    | exact resolve eq79 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq126 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq124
    | exact resolve eq124 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq127 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq126
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq126
    | exact resolve eq126 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq130 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq127 eq101
    | (have j0 := eq101 (σ y) (σ x)
       grind)
    | exact resolve eq101 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq130
    | exact resolve eq130 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq134 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq131
       have r₂ := eq27
       grind)
    | exact resolve eq131 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq136 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq134
    | exact resolve eq134 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq138 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq136 eq27
    | exact resolve eq27 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq976 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq136 eq85
    | (have r₁ := eq85
       have r₂ := eq136
       grind)
    | exact resolve eq85 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq136
  have eq977 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq976
  have eq980 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq977 eq127
    | exact resolve eq127 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq984 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq980
  have eq989 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq984
       have r₂ := eq138
       grind)
    | exact resolve eq984 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq984
  have eq993 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq989 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq989
       grind)
    | exact resolve eq13 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq1018 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq993
  have eq1019 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1018
    | exact resolve eq1018 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018
  have eq1233 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1019 eq127
    | exact resolve eq127 eq1019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq1019
  have eq1236 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1233
  have eq1240 : y = (M.op x y) := by
    first
    | (have r₁ := eq1236
       have r₂ := eq27
       grind)
    | exact resolve eq1236 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236
  have eq1242 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1240 eq20
    | exact resolve eq20 eq1240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1247 : y ≠ y ∨ y = (M.op y x) ∨ y = (k y x) := by
    first
    | exact superpose eq1240 eq84
    | (have r₁ := eq84
       have r₂ := eq1240
       grind)
    | exact resolve eq84 eq1240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq1251 : y = (k y x) ∨ y = (M.op y x) := by grind
  clear eq1247
  have eq1257 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1242
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1242
    | exact resolve eq1242 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242
  have eq1474 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1257 eq26
    | exact resolve eq26 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1987 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq79
       have i₂ := eq1251
       grind)
    | exact superpose eq1251 eq79
    | exact resolve eq79 eq1251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq1994 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1257 eq1987
    | exact resolve eq1987 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1987
  have eq1996 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1994
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1994
    | exact resolve eq1994 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1994
  have eq1997 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1257 eq1996
    | exact resolve eq1996 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1996
  have eq2000 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1997 eq101
    | (have j0 := eq101 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq101 eq1997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1997
  have eq2001 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by grind
  clear eq2000
  have eq2003 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1474 eq2001
    | exact resolve eq2001 eq1474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2001
  have eq2006 : y = (M.op y x) := by
    first
    | (have r₁ := eq2003
       have r₂ := eq27
       grind)
    | exact resolve eq2003 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2003
  have eq2011 : y ≠ y ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2006
       grind)
    | exact superpose eq2006 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2006
       grind)
    | exact resolve eq13 eq2006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2006
  have eq2031 : (M.op x y) = (k y x) := by grind
  clear eq2011
  have eq2038 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq2031
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2031
    | exact resolve eq2031 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2031
  have eq2043 : y = (k y x) := by
    first
    | exact superpose eq1240 eq2038
    | exact resolve eq2038 eq1240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240 eq2038
  have eq2078 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq79
       have i₂ := eq2043
       grind)
    | exact superpose eq2043 eq79
    | exact resolve eq79 eq2043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq2043
  have eq2085 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1257 eq2078
    | exact resolve eq2078 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2078
  have eq2087 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq2085
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2085
    | exact resolve eq2085 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2085
  have eq2088 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1257 eq2087
    | exact resolve eq2087 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257 eq2087
  have eq2091 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2088 eq101
    | (have j0 := eq101 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq101 eq2088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq2088
  have eq2092 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq2091
  have eq2094 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1474 eq2092
    | exact resolve eq2092 eq1474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474 eq2092
  have eq2097 : False := by grind
  exact eq2097

/-- `Equation3698`: `x ◇ x = (y ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pyx_y_pxy_y_pyx_Equation3698 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3698 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3698.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
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
  have eq61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq61 (σ X0)
       grind)
    | exact superpose eq61 eq15
    | exact resolve eq15 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq61 (τ X0)
       grind)
    | exact superpose eq61 eq18
    | exact resolve eq18 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq71 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq68
    | exact resolve eq68 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq75 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq61 X0
       grind)
    | exact superpose eq61 eq64
    | exact resolve eq64 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq79 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq61 X0
       grind)
    | exact superpose eq61 eq71
    | exact resolve eq71 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq71
  have eq85 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq10
    | exact resolve eq10 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq317 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X1 (σ X0)
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq85
    | (have j0 := eq85 X1 (σ X0)
       grind)
    | (have r₁ := eq85 X0 (σ X0)
       have r₂ := eq75 X0
       grind)
    | exact resolve eq85 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq324 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq317 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq317
    | (have j0 := eq317 X0 X1
       grind)
    | exact resolve eq317 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq365 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq373 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq388 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq373 X0 X1
       have i₂ := eq95 X1
       grind)
    | exact superpose eq95 eq373
    | (have j0 := eq373 X0 X1
       grind)
    | exact resolve eq373 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq373
  have eq396 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq365 X0 X1
       have i₂ := eq75 X1
       grind)
    | exact superpose eq75 eq365
    | (have j0 := eq365 X0 X1
       grind)
    | exact resolve eq365 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq414 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq396 X0 X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq396
    | (have j0 := eq396 X0 X1
       grind)
    | exact resolve eq396 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq1638 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq388 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq388
    | (have j0 := eq388 X1 (σ X0)
       grind)
    | exact resolve eq388 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq1696 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1638 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1638
    | (have j0 := eq1638 X0 X1
       grind)
    | exact resolve eq1638 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638
  have eq1699 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1696 X0 X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq1696
    | (have j0 := eq1696 X0 X1
       grind)
    | exact resolve eq1696 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1696
  have eq1700 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1699 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1699
    | (have j0 := eq1699 X0 X1
       grind)
    | exact resolve eq1699 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1699
  have eq10112 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq414 x y
       grind)
    | exact superpose eq414 eq16
    | (have j1 := eq414 x y
       grind)
    | exact resolve eq16 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10116 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq414 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq10856 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10112
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq10112
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq10112 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10112
  have eq10859 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq10856
  have eq20105 : (M.op y y) = (τ (σ (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq10859
       grind)
    | exact superpose eq10859 eq10
    | exact resolve eq10 eq10859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10859
  have eq20234 : (M.op x x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq20105
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq20105
    | exact resolve eq20105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20105
  have eq20235 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq20234
  have eq20237 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20235
       grind)
    | exact superpose eq20235 eq16
    | exact resolve eq16 eq20235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20238 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq20235
       grind)
    | exact superpose eq20235 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq20235
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20235
       grind)
    | exact resolve eq13 eq20235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20235
  have eq20239 : (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq20238
  have eq20240 : (σ x) = (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20239
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq20239
    | exact resolve eq20239 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20239
  have eq20242 : (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20240
       have i₂ := eq75 x
       grind)
    | exact superpose eq75 eq20240
    | exact resolve eq20240 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20240
  have eq20243 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ (k y x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20242
       have i₂ := eq75 y
       grind)
    | exact superpose eq75 eq20242
    | exact resolve eq20242 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq20242
  have eq20268 : (M.op y y) = (τ (σ (M.op x x))) ∨ (σ x) = (σ (k y x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq20243
       grind)
    | exact superpose eq20243 eq10
    | exact resolve eq10 eq20243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20243
  have eq20397 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ (k y x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20268
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq20268
    | exact resolve eq20268 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20268
  have eq20398 : (σ x) = (σ (k y x)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq20397
  have eq20402 : (σ (M.op x y)) = (σ x) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1700 y x
       have i₂ := eq20398
       grind)
    | exact superpose eq20398 eq1700
    | (have j0 := eq1700 x y
       grind)
    | exact resolve eq1700 eq20398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1700 eq20398
  have eq20491 : (σ (M.op x y)) = (σ x) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq20402
  have eq20550 : (M.op x x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20491
       have r₂ := eq20237
       grind)
    | exact resolve eq20491 eq20237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20237 eq20491
  have eq20555 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k X0 y) = (M.op X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq20550
       grind)
    | exact superpose eq20550 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq20550
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq20550
       grind)
    | exact resolve eq12 eq20550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20563 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq324 X0 y
       have i₂ := eq20550
       grind)
    | exact superpose eq20550 eq324
    | (have j0 := eq324 X0 x
       grind)
    | exact resolve eq324 eq20550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20550
  have eq20689 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq20555 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20555
  have eq20890 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq20563 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20563
  have eq20908 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20890
       grind)
    | exact superpose eq20890 eq16
    | exact resolve eq16 eq20890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20890
  have eq20956 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20908
       have i₂ := eq20689
       grind)
    | exact superpose eq20689 eq20908
    | exact resolve eq20908 eq20689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20689 eq20908
  have eq20959 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq20956
  have eq20960 : x = (M.op x y) := by grind
  clear eq20959
  have eq20961 : x ≠ x ∨ x = (k y x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq20960
       grind)
    | exact superpose eq20960 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20960
       grind)
    | exact resolve eq13 eq20960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20962 : (M.op x x) = (M.op y y) ∨ x = (k y x) := by grind
  clear eq20961
  have eq20964 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k X0 y) = (M.op X0 y) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq20962
       grind)
    | exact superpose eq20962 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq20962
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq20962
       grind)
    | exact resolve eq12 eq20962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20972 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq324 X0 y
       have i₂ := eq20962
       grind)
    | exact superpose eq20962 eq324
    | (have j0 := eq324 X0 x
       grind)
    | exact resolve eq324 eq20962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20962
  have eq21114 : (M.op x y) = (k x y) ∨ x = (k y x) := by
    first
    | (have j0 := eq20964 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20964
  have eq21118 : x = (k y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq21114
       have i₂ := eq20960
       grind)
    | exact superpose eq20960 eq21114
    | exact resolve eq21114 eq20960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21114
  have eq21147 : (σ x) ≠ (σ x) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq10116 x y
       have i₂ := eq21118
       grind)
    | exact superpose eq21118 eq10116
    | (have j0 := eq10116 x y
       grind)
    | exact resolve eq10116 eq21118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21118
  have eq21160 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by grind
  clear eq21147
  have eq21449 : (M.op y y) = (τ (σ (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq21160
       grind)
    | exact superpose eq21160 eq10
    | exact resolve eq10 eq21160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21160
  have eq21580 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq21449
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq21449
    | exact resolve eq21449 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21449
  have eq21584 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x x) = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21580
       grind)
    | exact superpose eq21580 eq16
    | exact resolve eq16 eq21580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21580
  have eq21588 : (σ x) ≠ (σ x) ∨ (M.op x x) = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq21584
       have i₂ := eq20960
       grind)
    | exact superpose eq20960 eq21584
    | exact resolve eq21584 eq20960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21584
  have eq21589 : (M.op x x) = (M.op y y) ∨ x = (k x y) := by grind
  clear eq21588
  have eq21594 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k X0 y) = (M.op X0 y) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq21589
       grind)
    | exact superpose eq21589 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq21589
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq21589
       grind)
    | exact resolve eq12 eq21589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21589
  have eq21851 : (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have j0 := eq21594 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21594
  have eq21857 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq21851
       have i₂ := eq20960
       grind)
    | exact superpose eq20960 eq21851
    | exact resolve eq21851 eq20960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21851
  have eq21858 : x = (k x y) := by grind
  clear eq21857
  have eq25159 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (k y x) := by
    first
    | (have j0 := eq20972 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20972
  have eq25171 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq25159
       have i₂ := eq21858
       grind)
    | exact superpose eq21858 eq25159
    | exact resolve eq25159 eq21858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25159
  have eq25186 : (σ (M.op x y)) ≠ (σ x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25171
       grind)
    | exact superpose eq25171 eq16
    | exact resolve eq16 eq25171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25171
  have eq25190 : (σ x) ≠ (σ x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq25186
       have i₂ := eq20960
       grind)
    | exact superpose eq20960 eq25186
    | exact resolve eq25186 eq20960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25186
  have eq25191 : x = (k y x) := by grind
  clear eq25190
  have eq25224 : (σ x) ≠ (σ x) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10116 x y
       have i₂ := eq25191
       grind)
    | exact superpose eq25191 eq10116
    | (have j0 := eq10116 x y
       grind)
    | exact resolve eq10116 eq25191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10116 eq25191
  have eq25237 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq25224
  have eq25446 : (M.op y y) = (τ (σ (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq25237
       grind)
    | exact superpose eq25237 eq10
    | exact resolve eq10 eq25237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25237
  have eq25579 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq25446
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq25446
    | exact resolve eq25446 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25446
  have eq25583 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25579
       grind)
    | exact superpose eq25579 eq16
    | exact resolve eq16 eq25579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25579
  have eq25587 : (σ x) ≠ (σ x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq25583
       have i₂ := eq20960
       grind)
    | exact superpose eq20960 eq25583
    | exact resolve eq25583 eq20960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25583
  have eq25588 : (M.op x x) = (M.op y y) := by grind
  clear eq25587
  have eq25599 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq324 X0 y
       have i₂ := eq25588
       grind)
    | exact superpose eq25588 eq324
    | (have j0 := eq324 X0 x
       grind)
    | exact resolve eq324 eq25588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324 eq25588
  have eq25924 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have j0 := eq25599 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25599
  have eq25936 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25924
       have i₂ := eq21858
       grind)
    | exact superpose eq21858 eq25924
    | exact resolve eq25924 eq21858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21858 eq25924
  have eq25948 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25936
       grind)
    | exact superpose eq25936 eq16
    | exact resolve eq16 eq25936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25936
  have eq25953 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq25948
       have i₂ := eq20960
       grind)
    | exact superpose eq20960 eq25948
    | exact resolve eq25948 eq20960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20960 eq25948
  have eq25954 : False := by grind
  exact eq25954

/-- `Equation3698`: `x ◇ x = (y ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_pyy_pxy_pxx_pxy_Equation3698 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3698 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3698.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X2) (M.op X1 X0)) := by
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
  have eq50 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X3 X4) (M.op X3 X2)) := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X2 X3) (M.op X2 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq14 X0 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op (M.op X2 X3) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op X2 X3) (M.op X2 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op x y) (M.op x X0)) := by
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
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X1 X0) (M.op X1 X2)) ∨ (M.op (M.op X1 X0) (M.op X1 X2)) = (k (M.op X1 X0) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 X0) (M.op X1 X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X1 X0) (M.op X1 X2)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq75 (σ X0)
       grind)
    | exact superpose eq75 eq10
    | exact resolve eq10 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq79 X0
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq79
    | exact resolve eq79 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq88 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq88
    | (have j0 := eq88 (σ X0) (σ X1)
       grind)
    | exact resolve eq88 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq88 x y
       grind)
    | exact superpose eq88 eq44
    | (have j1 := eq88 x y
       grind)
    | exact resolve eq44 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq103
    | exact resolve eq103 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
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
  have eq113 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq117 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq113
       have i₂ := eq75 sF3
       grind)
    | exact superpose eq75 eq113
    | exact resolve eq113 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq119 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq117
       have i₂ := eq75 y
       grind)
    | exact superpose eq75 eq117
    | exact resolve eq117 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq134 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) ≠ (M.op X3 X2) ∨ (M.op X3 X2) = (M.op X2 X3) ∨ (M.op X3 X3) = (k X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X2
       have i₂ := eq14 X2 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X2 X3
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq161 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq158
       have i₂ := eq75 sF1
       grind)
    | exact superpose eq75 eq158
    | exact resolve eq158 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq163 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq161
       have i₂ := eq75 sF0
       grind)
    | exact superpose eq75 eq161
    | exact resolve eq161 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq161
  have eq249 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op x y) (M.op x X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X2
       have i₂ := eq14 X2 X0 X1
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op x y) (M.op x (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op X1 X0)
       have i₂ := eq14 X0 X1 X0
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : (M.op y y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq54 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54
    | (have j0 := eq54 y
       grind)
    | exact resolve eq54 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op x y) (M.op x X0)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq55 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq55
    | (have j0 := eq55 (σ y)
       grind)
    | exact resolve eq55 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq285 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y y)) := by
    first
    | exact superpose eq251 eq163
    | exact resolve eq163 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq295 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq285
       have i₂ := eq119
       grind)
    | exact superpose eq119 eq285
    | exact resolve eq285 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq325 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq295 eq59
    | exact resolve eq59 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq327 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op (σ x) X0) (M.op (σ x) X0)) = (k (M.op (σ x) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq325 eq12
    | (have j0 := eq12 (M.op (σ x) X0) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq12 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op (σ x) X0) (M.op (σ x) X0)) = (k (M.op (σ x) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq269 eq327
    | (have j0 := eq327 X0
       grind)
    | exact resolve eq327 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq327
  have eq336 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op (σ x) X0) (M.op (σ x) X0)) = (k (M.op (σ x) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq333 X0
       grind)
    | (have r₁ := eq333 X0
       have r₂ := eq295
       grind)
    | exact resolve eq333 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq337 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (σ x) X0) (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq336 X0
       have i₂ := eq14 X0 sF2 X0
       grind)
    | exact superpose eq14 eq336
    | (have j0 := eq336 X0
       grind)
    | exact resolve eq336 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq606 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X0) x
       have i₂ := eq84 X0
       grind)
    | exact superpose eq84 eq14
    | exact resolve eq14 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq936 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op X2 X3) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 X1 X2 X3
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq54
  have eq1096 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq106 eq88
    | (have j0 := eq88 (σ x) (σ y)
       grind)
    | exact resolve eq88 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq1097 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq1096
    | exact resolve eq1096 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096
  have eq1100 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq1097
       have r₂ := eq27
       grind)
    | exact resolve eq1097 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097
  have eq1102 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq295 eq1100
    | exact resolve eq1100 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq1104 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq1102
    | exact resolve eq1102 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1414 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X3 X3) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op X4 X5) (M.op X6 X3))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq51 X3 X6 (M.op X4 X5) (M.op X4 X2)
       have i₂ := eq50 X4 X5 X2 X0 X1
       grind)
    | (have i₁ := eq51 X3 X6 (M.op X4 X5) (M.op X4 X2)
       have i₂ := eq50 X0 X1 X2 X4 X5
       grind)
    | exact superpose eq50 eq51
    | exact resolve eq51 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq51
  have eq2386 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X1
       have i₂ := eq84 X1
       grind)
    | exact superpose eq84 eq94
    | (have j0 := eq94 X0 X1
       grind)
    | exact resolve eq94 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq94
  have eq2425 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op y y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2386 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2386
    | (have j0 := eq2386 X0 y
       grind)
    | exact resolve eq2386 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2386
  have eq2487 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2425 X0
       have i₂ := eq119
       grind)
    | exact superpose eq119 eq2425
    | (have j0 := eq2425 X0
       grind)
    | exact resolve eq2425 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2425
  have eq2514 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq295 eq2487
    | (have j0 := eq2487 X0
       grind)
    | exact resolve eq2487 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2487
  have eq3303 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ≠ (M.op X1 (σ y)) ∨ (M.op X1 (σ y)) = (M.op (σ y) X1) ∨ (M.op X1 X1) = (k X1 (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq134
    | (have j0 := eq134 (σ x) X0 (σ y) X1
       grind)
    | exact resolve eq134 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq3362 : ∀ X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (M.op X1 (σ y)) ∨ (M.op X1 (σ y)) = (M.op (σ y) X1) ∨ (M.op X1 X1) = (k X1 (σ y)) := by
    intro X1
    first
    | exact superpose eq325 eq3303
    | (have j0 := eq3303 x X1
       grind)
    | exact resolve eq3303 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3303
  have eq3631 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (k (M.op (σ x) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq72
    | (have j0 := eq72 X0 (σ x) (σ y)
       grind)
    | exact resolve eq72 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq3665 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (k (M.op (σ x) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq325 eq3631
    | (have j0 := eq3631 X0
       grind)
    | (have r₁ := eq3631 (σ (M.op x y))
       have r₂ := eq325 (σ (M.op x y))
       grind)
    | exact resolve eq3631 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3631
  have eq3712 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (M.op (σ x) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq325 eq3665
    | (have j0 := eq3665 X0
       grind)
    | (have r₁ := eq3665 (M.op (σ x) (σ y))
       have r₂ := eq325 (σ y)
       grind)
    | exact resolve eq3665 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3665
  have eq48691 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (M.op (σ x) (M.op X1 X0)) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq3712 (M.op X1 X0)
       have i₂ := eq14 X0 X1 X0
       grind)
    | exact superpose eq14 eq3712
    | (have j0 := eq3712 X0
       grind)
    | (have r₁ := eq3712 (M.op X1 (σ (M.op x y)))
       have r₂ := eq14 (σ (M.op x y)) X1 (σ (M.op x y))
       grind)
    | exact resolve eq3712 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3712
  have eq66712 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (k (τ X0) y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2514 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2514
    | exact resolve eq2514 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2514
  have eq66840 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq66712 X0
       have i₂ := eq34 X0 y
       grind)
    | exact superpose eq34 eq66712
    | (have j0 := eq66712 X0
       grind)
    | exact resolve eq66712 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq66712
  have eq66863 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq66840 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq66840
    | (have j0 := eq66840 X0
       grind)
    | exact resolve eq66840 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq66840
  have eq67759 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = (k (M.op (σ x) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq266 eq337
    | (have j0 := eq337 X0
       grind)
    | exact resolve eq337 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq337
  have eq73498 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op X1 X0) (M.op X1 X0)) = (k (M.op (σ x) (M.op X1 X0)) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq67759 eq250
    | (have j1 := eq67759 (M.op X1 X0)
       grind)
    | exact resolve eq250 eq67759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq67759
  have eq73620 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (σ x) (M.op X1 X0)) (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq73498 X0 X1
       have i₂ := eq14 X0 X1 X0
       grind)
    | exact superpose eq14 eq73498
    | (have j0 := eq73498 X0 X1
       grind)
    | exact resolve eq73498 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73498
  have eq78420 : ∀ X2 X3 X4 X5 X6 : G, (M.op X3 X3) = (M.op (M.op (M.op x y) (M.op x X2)) (M.op (M.op X4 X5) (M.op X6 X3))) := by
    intro X2 X3 X4 X5 X6
    first
    | (have i₁ := eq1414 x x X2 X3 X4 X5 X6
       have i₂ := eq249 x x X2
       grind)
    | (have i₁ := eq1414 x y X2 X3 X4 X5 X6
       have i₂ := eq249 x x X2
       grind)
    | exact superpose eq249 eq1414
    | (have j0 := eq1414 x y X2 X3 X4 X5 X6
       grind)
    | exact resolve eq1414 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq1414
  have eq97791 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq3362
    | (have j0 := eq3362 (σ x)
       grind)
    | exact resolve eq3362 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3362
  have eq108413 : (M.op x y) ≠ (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq252 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq252
    | (have j0 := eq252 y x
       grind)
    | exact resolve eq252 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq108424 : (M.op x y) ≠ (M.op y y) ∨ (M.op x y) = (M.op y x) ∨ (k x y) = (M.op x x) := by
    first
    | exact superpose eq251 eq108413
    | exact resolve eq108413 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq108413
  have eq909505 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1104 eq66863
    | (have j0 := eq66863 X0
       grind)
    | exact resolve eq66863 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1243421 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq1104 eq97791
    | (have r₁ := eq97791
       have r₂ := eq1104
       grind)
    | exact resolve eq97791 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97791
  have eq1243422 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq1243421
  have eq1243430 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq1243422 eq106
    | exact resolve eq106 eq1243422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243422
  have eq1243465 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq1243430
  have eq1243565 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1243465 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1243465
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1243465
       grind)
    | exact resolve eq13 eq1243465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243465
  have eq1243973 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq909505 (σ x)
       grind)
    | (have r₁ := eq1243565
       have r₂ := eq909505 (σ x)
       grind)
    | exact resolve eq1243565 eq909505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909505 eq1243565
  have eq1244035 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq1243973
    | exact resolve eq1243973 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243973
  have eq1244124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1244035 eq106
    | exact resolve eq106 eq1244035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq1244035
  have eq1244160 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq1244124
  have eq1244187 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq1244160
       have r₂ := eq27
       grind)
    | exact resolve eq1244160 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244160
  have eq1244594 : ∀ X0 X1 X2 : G, (σ (M.op x y)) = (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op X1 X2) (σ (M.op x y)))) ∨ (M.op x y) = (M.op y y) := by
    intro X0 X1 X2
    first
    | exact superpose eq1244187 eq78420
    | exact resolve eq78420 eq1244187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78420 eq1244187
  have eq1245051 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq936 eq1244594
    | exact resolve eq1244594 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936 eq1244594
  have eq1248173 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq1245051 eq1104
    | exact resolve eq1104 eq1245051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104 eq1245051
  have eq1249242 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq1248173
  have eq1249401 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq1249242
       have r₂ := eq27
       grind)
    | exact resolve eq1249242 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249242
  have eq1249426 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq119
       have i₂ := eq1249401
       grind)
    | exact superpose eq1249401 eq119
    | exact resolve eq119 eq1249401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq1249443 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq108424
       have i₂ := eq1249401
       grind)
    | exact superpose eq1249401 eq108424
    | (have r₁ := eq108424
       have r₂ := eq1249401
       grind)
    | exact resolve eq108424 eq1249401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108424 eq1249401
  have eq1249747 : (M.op x y) = (M.op y x) ∨ (k x y) = (M.op x x) := by grind
  clear eq1249443
  have eq1249886 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq295 eq1249426
    | exact resolve eq1249426 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249426
  have eq1249989 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq1249886
    | exact resolve eq1249886 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249886
  have eq1435961 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (M.op x y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (M.op (σ x) (M.op X1 X0)) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq1249989 eq48691
    | (have j0 := eq48691 X0 X1
       grind)
    | exact resolve eq48691 eq1249989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48691
  have eq1435962 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (M.op (σ x) (M.op X1 X0)) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq1249989 eq1435961
    | (have j0 := eq1435961 X0 X1
       grind)
    | (have r₁ := eq1435961 (σ (M.op x y)) X1
       have r₂ := eq1249989
       grind)
    | exact resolve eq1435961 eq1249989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435961
  have eq1436174 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (M.op (σ x) (M.op X0 (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq295 eq1435962
    | (have j0 := eq1435962 (σ (M.op x y)) x
       grind)
    | exact resolve eq1435962 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq1435962
  have eq1436180 : ∀ X0 : G, (σ (M.op x y)) = (k (M.op (σ x) (M.op X0 (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq1436174 X0
       grind)
    | (have r₁ := eq1436174 X0
       have r₂ := eq1249989
       grind)
    | exact resolve eq1436174 eq1249989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1436174
  have eq1473233 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (σ x) (M.op X1 X0)) (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq1249989 eq73620
    | (have j0 := eq73620 X0 X1
       grind)
    | exact resolve eq73620 eq1249989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73620
  have eq1475590 : ∀ X0 : G, (M.op X0 (σ y)) = (k (M.op (σ x) (M.op X0 (σ y))) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq66863 eq1473233
    | (have j1 := eq66863 X0
       grind)
    | exact resolve eq1473233 eq66863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66863 eq1473233
  have eq1477108 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq1436180 eq1475590
    | (have j0 := eq1475590 X0
       grind)
    | exact resolve eq1475590 eq1436180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1436180 eq1475590
  have eq1477109 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ (M.op x y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq1477108 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477108
  have eq2436130 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1477109 eq65
    | (have j1 := eq1477109 (σ x)
       grind)
    | exact resolve eq65 eq1477109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq1477109
  have eq2436476 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2436130
    | exact resolve eq2436130 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2436130
  have eq2436519 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq2436476
    | exact resolve eq2436476 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2436476
  have eq2436546 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq2436519
       have r₂ := eq27
       grind)
    | exact resolve eq2436519 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2436519
  have eq2799926 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1249747
       have i₂ := eq2436546
       grind)
    | exact superpose eq2436546 eq1249747
    | exact resolve eq1249747 eq2436546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249747
  have eq2803526 : ∀ X0 : G, (σ (τ (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) X0) (σ (τ (M.op (σ x) (σ y))))) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq606 x x
       have i₂ := eq2799926
       grind)
    | exact superpose eq2799926 eq606
    | exact resolve eq606 eq2799926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606 eq2799926
  have eq2804547 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2803526 X0
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq2803526
    | exact resolve eq2803526 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2803526
  have eq2804659 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2804547 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2804547
    | (have j0 := eq2804547 X0
       grind)
    | exact resolve eq2804547 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2804547
  have eq2804719 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq325 eq2804659
    | exact resolve eq2804659 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325 eq2804659
  have eq2804750 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1249989 eq2804719
    | exact resolve eq2804719 eq1249989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249989 eq2804719
  have eq2804778 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq2804750
       have r₂ := eq27
       grind)
    | exact resolve eq2804750 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2804750
  have eq2804820 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2804778
       grind)
    | exact superpose eq2804778 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2804778
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2804778
       grind)
    | exact resolve eq13 eq2804778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2804778
  have eq2805279 : (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq2804820
       have r₂ := eq18
       grind)
    | exact resolve eq2804820 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2804820
  have eq2805359 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2805279
       have i₂ := eq2436546
       grind)
    | exact superpose eq2436546 eq2805279
    | exact resolve eq2805279 eq2436546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2436546 eq2805279
  have eq2805397 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2805359
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2805359
    | exact resolve eq2805359 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2805359
  have eq2806077 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2805397 eq15
    | exact resolve eq15 eq2805397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2805397
  have eq2806355 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq2806077
    | exact resolve eq2806077 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2806077
  have eq2806378 : False := by grind
  exact eq2806378

/-- `Equation3698`: `x ◇ x = (y ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else if m(X,X) = m(X,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pxy_pxx_y_pxy_Equation3698 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3698 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3698.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X2) (M.op X1 X0)) := by
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
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op x y) (M.op x X0)) := by
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
  have eq59 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X1 X0) (M.op X1 X0)) ∨ (M.op (M.op X1 X2) (M.op X1 X2)) = (k (M.op X1 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 X2) (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X1 X2) (M.op X1 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) ≠ (M.op X3 X2) ∨ (M.op X3 X3) = (k X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 X2
       have i₂ := eq14 X2 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X3 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 X2)) = (k (M.op X1 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq72 X0 X1 X2
       grind)
    | (have r₁ := eq72 X2 X1 X2
       have r₂ := eq14 X2 X1 X2
       grind)
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq78 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op X1 X2) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77 X0 X1 X2
       have i₂ := eq14 X2 X1 X2
       grind)
    | exact superpose eq14 eq77
    | exact resolve eq77 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq80 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq75 (σ X0)
       grind)
    | exact superpose eq75 eq10
    | exact resolve eq10 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq75 x
       grind)
    | exact superpose eq75 eq43
    | exact resolve eq43 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq82 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq75 sF2
       grind)
    | exact superpose eq75 eq49
    | exact resolve eq49 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq83 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq82
       have i₂ := eq75 x
       grind)
    | exact superpose eq75 eq82
    | exact resolve eq82 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq84 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq81
       have i₂ := eq75 sF2
       grind)
    | exact superpose eq75 eq81
    | exact resolve eq81 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq85 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
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
  clear eq80
  have eq100 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq104
    | exact resolve eq104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq109
    | exact resolve eq109 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq113 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq111
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq111
    | exact resolve eq111 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
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
  have eq121 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq125 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq121
       have i₂ := eq75 sF3
       grind)
    | exact superpose eq75 eq121
    | exact resolve eq121 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq127 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq125
       have i₂ := eq75 y
       grind)
    | exact superpose eq75 eq125
    | exact resolve eq125 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq150 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq153 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq150
       have i₂ := eq75 sF1
       grind)
    | exact superpose eq75 eq150
    | exact resolve eq150 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq155 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq153
       have i₂ := eq75 sF0
       grind)
    | exact superpose eq75 eq153
    | exact resolve eq153 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq253 : (M.op y y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq54 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54
    | (have j0 := eq54 y
       grind)
    | exact resolve eq54 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op x y) (M.op x X0)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y y)) := by
    first
    | exact superpose eq253 eq155
    | exact resolve eq155 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq267
       have i₂ := eq127
       grind)
    | exact superpose eq127 eq267
    | exact resolve eq267 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq317 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq275 eq59
    | exact resolve eq59 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq400 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq75 (τ X0)
       grind)
    | exact superpose eq75 eq34
    | exact resolve eq34 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq411 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq400 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq400
    | exact resolve eq400 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq415 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq411 X0
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq411
    | exact resolve eq411 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq411
  have eq649 : ∀ X0 : G, (M.op y y) = (k (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq78 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq78
    | (have j0 := eq78 X0 x y
       grind)
    | exact resolve eq78 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : ∀ X0 : G, (M.op (σ y) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq78
    | (have j0 := eq78 X0 (σ x) (σ y)
       grind)
    | exact resolve eq78 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq275 eq652
    | exact resolve eq652 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq1209 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (M.op x y) (M.op x (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq415 X0
       have i₂ := eq54 (τ X0)
       grind)
    | exact superpose eq54 eq415
    | exact resolve eq415 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq415
  have eq2878 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ≠ (M.op X1 (σ y)) ∨ (M.op X1 X1) = (k X1 (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq73
    | (have j0 := eq73 (σ x) X0 (σ y) X1
       grind)
    | exact resolve eq73 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq2963 : ∀ X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (M.op X1 (σ y)) ∨ (M.op X1 X1) = (k X1 (σ y)) := by
    intro X1
    first
    | exact superpose eq317 eq2878
    | (have j0 := eq2878 x X1
       grind)
    | exact resolve eq2878 eq317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317 eq2878
  have eq4316 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq100 X0 X1
       have i₂ := eq85 X0
       grind)
    | exact superpose eq85 eq100
    | (have j0 := eq100 X0 X1
       grind)
    | exact resolve eq100 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq4317 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4316 X0 X1
       have i₂ := eq85 X1
       grind)
    | exact superpose eq85 eq4316
    | (have j0 := eq4316 X0 X1
       grind)
    | exact resolve eq4316 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4316
  have eq4607 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4317 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4317
  have eq6099 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (M.op (M.op x y) (M.op x (τ (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq1209 (σ X0)
       grind)
    | exact superpose eq1209 eq85
    | exact resolve eq85 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq1209
  have eq6124 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq6099 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq6099
    | exact resolve eq6099 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6099
  have eq11295 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq2963
    | (have j0 := eq2963 (σ x)
       grind)
    | exact resolve eq2963 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2963
  have eq24730 : (M.op x y) ≠ (M.op (M.op x y) (M.op x y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq255 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq255
    | (have j0 := eq255 y x
       grind)
    | exact resolve eq255 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq24740 : (M.op x y) ≠ (M.op y y) ∨ (k x y) = (M.op x x) := by
    first
    | exact superpose eq253 eq24730
    | exact resolve eq24730 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq24730
  have eq216196 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq216245 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq216196
    | exact resolve eq216196 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216196
  have eq216264 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq216245
       have r₂ := eq27
       grind)
    | exact resolve eq216245 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216245
  have eq216270 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq216264
    | exact resolve eq216264 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216264
  have eq216274 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq275 eq216270
    | exact resolve eq216270 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216270
  have eq216276 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq216274
    | exact resolve eq216274 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216274
  have eq216488 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq216276 eq78
    | exact resolve eq78 eq216276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216276
  have eq216567 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq696 eq216488
    | exact resolve eq216488 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216488
  have eq216568 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq216567
  have eq216691 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq216568 eq11295
    | (have r₁ := eq11295
       have r₂ := eq216568
       grind)
    | exact resolve eq11295 eq216568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11295 eq216568
  have eq216953 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq216691
  have eq222659 : (k x y) = (τ (M.op (σ x) (σ x))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq216953 eq65
    | exact resolve eq65 eq216953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq216953
  have eq222723 : (k x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq83 eq222659
    | exact resolve eq222659 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq222659
  have eq222741 : (k x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq222723
       have r₂ := eq24740
       grind)
    | exact resolve eq222723 eq24740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222723
  have eq222765 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq222741
       grind)
    | exact superpose eq222741 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq222741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222779 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq4607 x y
       have i₂ := eq222741
       grind)
    | exact superpose eq222741 eq4607
    | (have j0 := eq4607 x y
       grind)
    | exact resolve eq4607 eq222741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222741
  have eq222790 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq222779
  have eq222791 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq222765
  have eq222803 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq222790
       have i₂ := eq84
       grind)
    | exact superpose eq84 eq222790
    | exact resolve eq222790 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222790
  have eq222812 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq222791
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq222791
    | exact resolve eq222791 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222791
  have eq222813 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq222812
  have eq222834 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq222803
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq222803
    | exact resolve eq222803 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222803
  have eq222843 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq222813
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq222813
    | exact resolve eq222813 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq222813
  have eq222855 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq222834
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq222834
    | exact resolve eq222834 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222834
  have eq222869 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq222855
    | exact resolve eq222855 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222855
  have eq222882 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq222869
       have i₂ := eq127
       grind)
    | exact superpose eq127 eq222869
    | exact resolve eq222869 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222869
  have eq222895 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq275 eq222882
    | exact resolve eq222882 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222882
  have eq222908 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq222895
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq222895
    | exact resolve eq222895 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222895
  have eq222921 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq222908
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq222908
    | exact resolve eq222908 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222908
  have eq222934 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq222921
    | exact resolve eq222921 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222921
  have eq222990 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq127
       have i₂ := eq222843
       grind)
    | exact superpose eq222843 eq127
    | exact resolve eq127 eq222843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222843
  have eq223385 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq275 eq222990
    | exact resolve eq222990 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222990
  have eq223412 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq223385
    | exact resolve eq223385 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223385
  have eq323946 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq222934 eq78
    | exact resolve eq78 eq222934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222934
  have eq324086 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq696 eq323946
    | exact resolve eq323946 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696 eq323946
  have eq324087 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq324086
  have eq324237 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq324087 eq223412
    | exact resolve eq223412 eq324087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223412 eq324087
  have eq324657 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq324237
  have eq324710 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq324657
       have r₂ := eq27
       grind)
    | exact resolve eq324657 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324657
  have eq324749 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq84
       have i₂ := eq324710
       grind)
    | exact superpose eq324710 eq84
    | exact resolve eq84 eq324710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324900 : (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq6124 x
       have i₂ := eq324710
       grind)
    | exact superpose eq324710 eq6124
    | exact resolve eq6124 eq324710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6124
  have eq325022 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq78 X0 x x
       have i₂ := eq324710
       grind)
    | exact superpose eq324710 eq78
    | exact resolve eq78 eq324710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq325106 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq649 eq325022
    | exact resolve eq325022 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq325022
  have eq325171 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq155 eq324900
    | exact resolve eq324900 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq324900
  have eq325236 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq324749
    | exact resolve eq324749 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324749
  have eq325260 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq325171
    | exact resolve eq325171 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325171
  have eq325316 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq24740
       have i₂ := eq325106
       grind)
    | exact superpose eq325106 eq24740
    | (have r₁ := eq24740
       have r₂ := eq325106
       grind)
    | exact resolve eq24740 eq325106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24740 eq325106
  have eq325645 : (k x y) = (M.op x x) := by grind
  clear eq325316
  have eq325758 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq325645
       have i₂ := eq324710
       grind)
    | exact superpose eq324710 eq325645
    | exact resolve eq325645 eq324710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324710 eq325645
  have eq327016 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4607 x y
       have i₂ := eq325758
       grind)
    | exact superpose eq325758 eq4607
    | (have j0 := eq4607 x y
       grind)
    | exact resolve eq4607 eq325758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4607 eq325758
  have eq327039 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq327016
       have i₂ := eq84
       grind)
    | exact superpose eq84 eq327016
    | exact resolve eq327016 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327016
  have eq327072 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq325236 eq327039
    | (have r₁ := eq327039
       have r₂ := eq325236
       grind)
    | exact resolve eq327039 eq325236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327039
  have eq327098 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq327072
       have r₂ := eq20
       grind)
    | exact resolve eq327072 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq327072
  have eq327123 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq327098
       have i₂ := eq84
       grind)
    | exact superpose eq84 eq327098
    | exact resolve eq327098 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq327098
  have eq327145 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq325236 eq327123
    | exact resolve eq327123 eq325236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325236 eq327123
  have eq327166 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq327145
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq327145
    | exact resolve eq327145 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327145
  have eq327187 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq327166
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq327166
    | exact resolve eq327166 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327166
  have eq327208 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq26 eq327187
    | exact resolve eq327187 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327187
  have eq327229 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq327208
       have r₂ := eq27
       grind)
    | exact resolve eq327208 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327208
  have eq327250 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq327229
       have i₂ := eq127
       grind)
    | exact superpose eq127 eq327229
    | exact resolve eq327229 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq327229
  have eq327271 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq275 eq327250
    | exact resolve eq327250 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq327250
  have eq327292 : (M.op (σ x) (σ y)) = (σ (M.op x y)) := by
    first
    | exact superpose eq325260 eq327271
    | exact resolve eq327271 eq325260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325260 eq327271
  have eq327313 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq327292
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq327292
    | exact resolve eq327292 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq327292
  have eq327334 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq327313
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq327313
    | exact resolve eq327313 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq327313
  have eq327355 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq327334
    | exact resolve eq327334 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq327334
  have eq327373 : False := by grind
  exact eq327373

/-- `Equation3698`: `x ◇ x = (y ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pyx_pxx_pyx_Equation3698 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3698 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3698.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq40 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq12 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq53 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 (M.op X0 X1) (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq53
    | (have j0 := eq53 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq53 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (τ X0) = (τ X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq53 (τ X1) (τ X0)
       grind)
    | exact superpose eq53 eq44
    | (have j1 := eq53 (τ X0) (τ X1)
       grind)
    | exact resolve eq44 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq53
  have eq552 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67 y x
       grind)
    | exact superpose eq67 eq16
    | (have j1 := eq67 x y
       grind)
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq724 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq40 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq917 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq42 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq922 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq917 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq917
    | exact resolve eq917 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq944 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq922 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq922
    | exact resolve eq922 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq974 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq944 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq944
    | exact resolve eq944 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq1046 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq724 X0
       have i₂ := eq974 X0
       grind)
    | exact superpose eq974 eq724
    | exact resolve eq724 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724 eq974
  have eq213200 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1
       have i₂ := eq79 X0 X1
       grind)
    | (have i₁ := eq11 X0
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq11
    | (have j1 := eq79 X0 X1
       grind)
    | exact resolve eq11 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq213306 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq213200 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq213200
    | (have j0 := eq213200 X0 X1
       grind)
    | exact resolve eq213200 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213200
  have eq213383 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq213306 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq213306
    | (have j0 := eq213306 (τ (k (σ X0) X1)) (M.op (τ X1) X0)
       grind)
    | exact resolve eq213306 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213306
  have eq213780 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq213383 X0 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq213383
    | (have j0 := eq213383 X0 X1
       grind)
    | exact resolve eq213383 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq213383
  have eq213816 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq213780 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq213780
    | (have j0 := eq213780 X0 (σ X1)
       grind)
    | exact resolve eq213780 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213780
  have eq213993 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq552
       have i₂ := eq213816 x y
       grind)
    | exact superpose eq213816 eq552
    | (have j1 := eq213816 x y
       grind)
    | (have r₁ := eq552
       have r₂ := eq213816 (M.op x y) (k y x)
       grind)
    | (have r₁ := eq552
       have r₂ := eq213816 (k y x) (M.op x y)
       grind)
    | exact resolve eq552 eq213816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq213816
  have eq213994 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq213993
  have eq213995 : (σ x) = (σ y) := by grind
  clear eq213994
  have eq215701 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq213995
       grind)
    | exact superpose eq213995 eq10
    | exact resolve eq10 eq213995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213995
  have eq215804 : x = y := by
    first
    | (have i₁ := eq215701
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq215701
    | exact resolve eq215701 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215701
  have eq215837 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq215804
       grind)
    | exact superpose eq215804 eq16
    | exact resolve eq16 eq215804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215804
  have eq215838 : False := by grind
  exact eq215838

/-- `Equation3698`: `x ◇ x = (y ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyx_pyx_pxx_pyx_Equation3698 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3698 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3698.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq33 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq33 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq33 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X0 X1
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
  have eq58 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq60 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq61 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq62 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       have j1 := eq12 X1 X1
       grind)
    | (have r₁ := eq58 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq58 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq59 X0 X1
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq59 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq59 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq61 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq61 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq76 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       have j1 := eq62 X1 X0
       grind)
    | (have r₁ := eq66 X1 X1
       have r₂ := eq62 X0 X1
       grind)
    | exact resolve eq66 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq66
  have eq77 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 X1
       have i₂ := eq35 X1
       grind)
    | exact superpose eq35 eq70
    | (have j0 := eq70 X0 X1
       grind)
    | exact resolve eq70 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq70
  have eq556 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq562 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq556 X0 X1
       have j1 := eq77 X1 X0
       grind)
    | (have r₁ := eq556 X1 X1
       have r₂ := eq77 X1 X1
       grind)
    | (have r₁ := eq556 X1 X0
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq556 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq556
  have eq589 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq562 (σ X1) (σ X0)
       grind)
    | exact superpose eq562 eq15
    | exact resolve eq15 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq592 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq589 X0 X1
       have i₂ := eq562 X1 X0
       grind)
    | exact superpose eq562 eq589
    | exact resolve eq589 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562 eq589
  have eq595 : False := by grind
  exact eq595

/-- `Equation3698`: `x ◇ x = (y ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_pxy_pxx_pxy_Equation3698 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3698 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3698.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X2) (M.op X1 X0)) := by
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
  have eq50 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X3 X4) (M.op X3 X2)) := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X2 X3) (M.op X2 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq14 X0 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op (M.op X2 X3) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op X2 X3) (M.op X2 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op x y) (M.op x X0)) := by
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
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq84 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X0 X0) X0
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq84
    | (have j0 := eq84 (σ X0) (σ X1)
       grind)
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq84 x y
       grind)
    | exact superpose eq84 eq44
    | (have j1 := eq84 x y
       grind)
    | exact resolve eq44 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
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
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
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
  have eq124 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) ≠ (M.op X3 X2) ∨ (M.op X2 X3) = X2 ∨ (M.op X3 X3) = (k X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X2
       have i₂ := eq14 X2 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X3 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq126 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq126 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq126 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq132 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq128 (σ X0)
       grind)
    | exact superpose eq128 eq10
    | exact resolve eq10 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq128 x
       grind)
    | exact superpose eq128 eq43
    | exact resolve eq43 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq134 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq82
       have i₂ := eq128 y
       grind)
    | exact superpose eq128 eq82
    | exact resolve eq82 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq139 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq134
       have i₂ := eq128 sF3
       grind)
    | exact superpose eq128 eq134
    | exact resolve eq134 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq140 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq133
       have i₂ := eq128 sF2
       grind)
    | exact superpose eq128 eq133
    | exact resolve eq133 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq141 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq132 X0
       have i₂ := eq128 X0
       grind)
    | exact superpose eq128 eq132
    | exact resolve eq132 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq164 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq167 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq164
       have i₂ := eq128 sF1
       grind)
    | exact superpose eq128 eq164
    | exact resolve eq164 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq170 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq167
       have i₂ := eq128 sF0
       grind)
    | exact superpose eq128 eq167
    | exact resolve eq167 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq167
  have eq265 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op x y) (M.op x X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X2
       have i₂ := eq14 X2 X0 X1
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op x y) (M.op x (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op X1 X0)
       have i₂ := eq14 X0 X1 X0
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : (M.op y y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq54 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54
    | (have j0 := eq54 y
       grind)
    | exact resolve eq54 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op x y) (M.op x X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : (σ (M.op y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq267 eq170
    | exact resolve eq170 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq291 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq282
       have i₂ := eq139
       grind)
    | exact superpose eq139 eq282
    | exact resolve eq282 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq292 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq55 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq295 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq55
    | (have j0 := eq55 (σ y)
       grind)
    | exact resolve eq55 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq291 eq59
    | exact resolve eq59 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq339 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) ∨ (M.op (M.op (σ x) X0) (M.op (σ x) X0)) = (k (M.op (σ x) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq337 eq12
    | (have j0 := eq12 (M.op (σ x) X0) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq12 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) ∨ (M.op (M.op (σ x) X0) (M.op (σ x) X0)) = (k (M.op (σ x) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq295 eq339
    | (have j0 := eq339 X0
       grind)
    | exact resolve eq339 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq339
  have eq347 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) ∨ (M.op (M.op (σ x) X0) (M.op (σ x) X0)) = (k (M.op (σ x) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq344 X0
       grind)
    | (have r₁ := eq344 X0
       have r₂ := eq291
       grind)
    | exact resolve eq344 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq348 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (σ x) X0) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq347 X0
       have i₂ := eq14 X0 sF2 X0
       grind)
    | exact superpose eq14 eq347
    | (have j0 := eq347 X0
       grind)
    | exact resolve eq347 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq624 : (σ (M.op (k x y) (k x y))) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq141 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq141
    | exact resolve eq141 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : (σ (M.op (k x y) (k x y))) = (M.op (M.op x y) (M.op x (k (σ x) (σ y)))) := by
    first
    | (have i₁ := eq624
       have i₂ := eq54 (k sF2 sF3)
       grind)
    | exact superpose eq54 eq624
    | exact resolve eq624 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq674 : (M.op (M.op x y) (M.op x (k (σ x) (σ y)))) = (σ (M.op (M.op x y) (M.op x (k x y)))) := by
    first
    | (have i₁ := eq658
       have i₂ := eq54 (k x y)
       grind)
    | exact superpose eq54 eq658
    | exact resolve eq658 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq691 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op X1 X2) (M.op X1 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 X0 X3 X1 X2
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq51
    | exact resolve eq51 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq874 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op X2 X3) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 X1 X2 X3
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq903 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X0 X0)) = (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X3 (M.op (M.op X1 X2) X0) x x
       have i₂ := eq53 x X0 X1 X2
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq961 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 X3) (M.op X0 X0)) := by
    intro X0 X3
    first
    | (have i₁ := eq903 X0 x x X3
       have i₂ := eq14 X0 (M.op x x) X0
       grind)
    | exact superpose eq14 eq903
    | exact resolve eq903 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq1158 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq116 eq84
    | (have j0 := eq84 (σ x) (σ y)
       grind)
    | exact resolve eq84 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq1159 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq1158
    | exact resolve eq1158 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158
  have eq1162 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq1159
       have r₂ := eq27
       grind)
    | exact resolve eq1159 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159
  have eq1164 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq291 eq1162
    | exact resolve eq1162 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq1166 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq1164
    | exact resolve eq1164 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164
  have eq1421 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X3 X3) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op X4 X5) (M.op X6 X3))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq51 X3 X6 (M.op X4 X5) (M.op X4 X2)
       have i₂ := eq50 X4 X5 X2 X0 X1
       grind)
    | (have i₁ := eq51 X3 X6 (M.op X4 X5) (M.op X4 X2)
       have i₂ := eq50 X0 X1 X2 X4 X5
       grind)
    | exact superpose eq50 eq51
    | exact resolve eq51 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq2319 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq100 X0 X1
       have i₂ := eq141 X1
       grind)
    | exact superpose eq141 eq100
    | (have j0 := eq100 X0 X1
       grind)
    | exact resolve eq100 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq2338 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2319 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2319
    | (have j0 := eq2319 x X0
       grind)
    | exact resolve eq2319 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2387 : ∀ X0 X1 X2 X3 : G, (M.op (σ X1) (σ X1)) = (M.op (M.op X2 X3) (M.op X2 (σ (k X0 X1)))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 (σ X1) (σ X0) X2 X3
       have i₂ := eq2319 X0 X1
       grind)
    | exact superpose eq2319 eq51
    | (have j1 := eq2319 X0 X1
       grind)
    | exact resolve eq51 eq2319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2398 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2319 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319
  have eq2400 : ∀ X0 X1 X2 X3 : G, (σ (M.op X1 X1)) = (M.op (M.op X2 X3) (M.op X2 (σ (k X0 X1)))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2387 X0 X1 X2 X3
       have i₂ := eq141 X1
       grind)
    | exact superpose eq141 eq2387
    | (have j0 := eq2387 X0 X1 X2 X3
       grind)
    | exact resolve eq2387 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq2387
  have eq3273 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) ≠ (M.op X1 (σ y)) ∨ (σ y) = (M.op (σ y) X1) ∨ (M.op X1 X1) = (k X1 (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq124
    | (have j0 := eq124 (σ x) X0 (σ y) X1
       grind)
    | exact resolve eq124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq3354 : ∀ X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (M.op X1 (σ y)) ∨ (σ y) = (M.op (σ y) X1) ∨ (M.op X1 X1) = (k X1 (σ y)) := by
    intro X1
    first
    | exact superpose eq337 eq3273
    | (have j0 := eq3273 x X1
       grind)
    | exact resolve eq3273 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337 eq3273
  have eq25814 : ∀ X0 X3 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op x y) (M.op x (M.op X3 X0))) := by
    intro X0 X3
    first
    | (have i₁ := eq691 X0 x x X3
       have i₂ := eq265 x x (M.op X3 X0)
       grind)
    | (have i₁ := eq691 X0 x y X3
       have i₂ := eq265 X0 x (M.op X3 X0)
       grind)
    | exact superpose eq265 eq691
    | (have j0 := eq691 X0 x y X3
       grind)
    | exact resolve eq691 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq25815 : ∀ X0 X3 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x y) (M.op x (M.op X3 X0))) := by
    intro X0 X3
    first
    | exact superpose eq292 eq25814
    | exact resolve eq25814 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25814
  have eq48000 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (σ x) X0) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq292 eq348
    | (have j0 := eq348 X0
       grind)
    | exact resolve eq348 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292 eq348
  have eq49212 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op (σ x) (M.op X0 (M.op X1 X2))) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X2 X1 X0 (M.op X1 X2)
       have i₂ := eq48000 (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq48000 eq51
    | (have j1 := eq48000 (M.op X0 (M.op X1 X2))
       grind)
    | exact resolve eq51 eq48000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq49216 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (σ x) (M.op X0 X0)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq961 X0 X0
       have i₂ := eq48000 (M.op X0 X0)
       grind)
    | exact superpose eq48000 eq961
    | (have j1 := eq48000 (M.op X0 X0)
       grind)
    | exact resolve eq961 eq48000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961 eq48000
  have eq49268 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (σ x) (M.op X0 X0)) (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq266 eq49216
    | (have j0 := eq49216 X0
       grind)
    | exact resolve eq49216 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49216
  have eq49272 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x (M.op X1 X2))) ∨ (M.op X2 X2) = (k (M.op (σ x) (M.op X0 (M.op X1 X2))) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq25815 eq49212
    | (have j0 := eq49212 X0 X1 X2
       grind)
    | exact resolve eq49212 eq25815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49212
  have eq49353 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k (M.op (σ x) (M.op X0 (M.op X1 X2))) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq25815 eq49272
    | (have j0 := eq49272 X0 X1 X2
       grind)
    | exact resolve eq49272 eq25815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25815 eq49272
  have eq69910 : ∀ X0 : G, (σ (k x X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ x) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2338 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2338
  have eq75009 : ∀ X2 X3 X4 X5 X6 : G, (M.op X3 X3) = (M.op (M.op (M.op x y) (M.op x X2)) (M.op (M.op X4 X5) (M.op X6 X3))) := by
    intro X2 X3 X4 X5 X6
    first
    | (have i₁ := eq1421 x x X2 X3 X4 X5 X6
       have i₂ := eq265 x x X2
       grind)
    | (have i₁ := eq1421 x y X2 X3 X4 X5 X6
       have i₂ := eq265 x x X2
       grind)
    | exact superpose eq265 eq1421
    | (have j0 := eq1421 x y X2 X3 X4 X5 X6
       grind)
    | exact resolve eq1421 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421
  have eq77666 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2398 (τ X0) X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq2398
    | (have j0 := eq2398 (τ X0) X1
       grind)
    | exact resolve eq2398 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq2398
  have eq77832 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ (σ (M.op X1 X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq77666 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq77666
    | (have j0 := eq77666 X0 X1
       grind)
    | exact resolve eq77666 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77666
  have eq78090 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq3354
    | (have j0 := eq3354 (σ x)
       grind)
    | exact resolve eq3354 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3354
  have eq84050 : (M.op x y) ≠ (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq268 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq268
    | (have j0 := eq268 y x
       grind)
    | exact resolve eq268 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq84060 : (M.op x y) ≠ (M.op y y) ∨ y = (M.op y x) ∨ (k x y) = (M.op x x) := by
    first
    | exact superpose eq267 eq84050
    | exact resolve eq84050 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267 eq84050
  have eq130130 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (M.op x y) (M.op x (σ (k X0 X1)))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2400 X0 X1 x x
       have i₂ := eq265 x x (σ (k X0 X1))
       grind)
    | (have i₁ := eq2400 X0 X1 x y
       have i₂ := eq265 X0 X1 (σ (k X0 X1))
       grind)
    | exact superpose eq265 eq2400
    | (have j0 := eq2400 X0 X1 x y
       grind)
    | exact resolve eq2400 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq2400
  have eq130365 : (σ (M.op y y)) = (M.op (M.op x y) (M.op x (k (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq130130 x y
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq130130
    | (have j0 := eq130130 x y
       grind)
    | exact resolve eq130130 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130130
  have eq130627 : (M.op (σ y) (σ y)) = (M.op (M.op x y) (M.op x (k (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq130365
       have i₂ := eq139
       grind)
    | exact superpose eq139 eq130365
    | exact resolve eq130365 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130365
  have eq130817 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (M.op x (k (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq291 eq130627
    | exact resolve eq130627 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130627
  have eq130994 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (M.op x (k (σ x) (σ y)))) := by
    first
    | (have i₁ := eq130817
       have i₂ := eq139
       grind)
    | exact superpose eq139 eq130817
    | exact resolve eq130817 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130817
  have eq131108 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (M.op x (k (σ x) (σ y)))) := by
    first
    | exact superpose eq291 eq130994
    | exact resolve eq130994 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130994
  have eq131201 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (M.op x (k (σ x) (σ y)))) := by
    first
    | (have i₁ := eq131108
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq131108
    | exact resolve eq131108 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131108
  have eq131256 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (M.op x (k (σ x) (σ y)))) := by
    first
    | (have i₁ := eq131201
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq131201
    | exact resolve eq131201 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131201
  have eq131289 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (M.op x (k (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq131256
    | exact resolve eq131256 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131256
  have eq1054130 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq1166 eq78090
    | (have r₁ := eq78090
       have r₂ := eq1166
       grind)
    | exact resolve eq78090 eq1166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78090
  have eq1054131 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq1054130
  have eq1054139 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq1054131 eq116
    | exact resolve eq116 eq1054131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054131
  have eq1054171 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq1054139
  have eq1054260 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1054171 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1054171
       grind)
    | exact resolve eq13 eq1054171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054171
  have eq1054495 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq1054260
  have eq1054612 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq1054495
    | exact resolve eq1054495 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054495
  have eq1055241 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1054612 eq116
    | exact resolve eq116 eq1054612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq1054612
  have eq1055274 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq1055241
  have eq1055298 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq1055274
       have r₂ := eq27
       grind)
    | exact resolve eq1055274 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055274
  have eq1055662 : ∀ X0 X1 X2 : G, (σ (M.op x y)) = (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op X1 X2) (σ (M.op x y)))) ∨ (M.op x y) = (M.op y y) := by
    intro X0 X1 X2
    first
    | exact superpose eq1055298 eq75009
    | exact resolve eq75009 eq1055298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75009 eq1055298
  have eq1056059 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq874 eq1055662
    | exact resolve eq1055662 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874 eq1055662
  have eq1057276 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq1056059 eq1166
    | exact resolve eq1166 eq1056059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166 eq1056059
  have eq1058208 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq1057276
  have eq1058358 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq1058208
       have r₂ := eq27
       grind)
    | exact resolve eq1058208 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058208
  have eq1061102 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq139
       have i₂ := eq1058358
       grind)
    | exact superpose eq1058358 eq139
    | exact resolve eq139 eq1058358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1061115 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq84060
       have i₂ := eq1058358
       grind)
    | exact superpose eq1058358 eq84060
    | (have r₁ := eq84060
       have r₂ := eq1058358
       grind)
    | exact resolve eq84060 eq1058358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84060 eq1058358
  have eq1061388 : (k x y) = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq1061115
  have eq1061521 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq291 eq1061102
    | exact resolve eq1061102 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061102
  have eq1061617 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq1061521
    | exact resolve eq1061521 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061521
  have eq1065631 : (σ (M.op x y)) = (k (M.op (σ x) (σ (M.op x y))) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1061617 eq49268
    | exact resolve eq49268 eq1061617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49268
  have eq1066045 : (σ (M.op x y)) = (k (M.op (σ x) (σ (M.op x y))) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq1065631
       have r₂ := eq27
       grind)
    | exact resolve eq1065631 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065631
  have eq1256031 : (k (σ x) (σ y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq69910 y
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq69910
    | (have j0 := eq69910 y
       grind)
    | exact resolve eq69910 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69910
  have eq1256341 : (k (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op y y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1256031
       have i₂ := eq139
       grind)
    | exact superpose eq139 eq1256031
    | exact resolve eq1256031 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256031
  have eq1256413 : (k (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op y y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq291 eq1256341
    | exact resolve eq1256341 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256341
  have eq1256461 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ (M.op y y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1061617 eq1256413
    | exact resolve eq1256413 eq1061617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256413
  have eq1256509 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1256461
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1256461
    | exact resolve eq1256461 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256461
  have eq1256537 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1256509
       have i₂ := eq139
       grind)
    | exact superpose eq139 eq1256509
    | exact resolve eq1256509 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256509
  have eq1256562 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) := by
    first
    | exact superpose eq291 eq1256537
    | exact resolve eq1256537 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256537
  have eq1256580 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) := by
    first
    | exact superpose eq1061617 eq1256562
    | exact resolve eq1256562 eq1061617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256562
  have eq1256597 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1256580
    | exact resolve eq1256580 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256580
  have eq1256607 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq1256597
       have r₂ := eq27
       grind)
    | exact resolve eq1256597 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256597
  have eq1262451 : ∀ X0 : G, (σ (M.op y y)) ≠ (k X0 (σ y)) ∨ (σ (M.op y y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq77832 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq77832
    | (have j0 := eq77832 X0 y
       grind)
    | exact resolve eq77832 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq77832
  have eq1262788 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (k X0 (σ y)) ∨ (σ (M.op y y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1262451 X0
       have i₂ := eq139
       grind)
    | exact superpose eq139 eq1262451
    | (have j0 := eq1262451 X0
       grind)
    | exact resolve eq1262451 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262451
  have eq1263088 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (k X0 (σ y)) ∨ (σ (M.op y y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq291 eq1262788
    | (have j0 := eq1262788 X0
       grind)
    | exact resolve eq1262788 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262788
  have eq1263364 : ∀ X0 : G, (σ (M.op x y)) ≠ (k X0 (σ y)) ∨ (σ (M.op y y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq1061617 eq1263088
    | (have j0 := eq1263088 X0
       grind)
    | exact resolve eq1263088 eq1061617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263088
  have eq1263634 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) ≠ (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1263364 X0
       have i₂ := eq139
       grind)
    | exact superpose eq139 eq1263364
    | (have j0 := eq1263364 X0
       grind)
    | exact resolve eq1263364 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq1263364
  have eq1263877 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) ≠ (k X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq291 eq1263634
    | (have j0 := eq1263634 X0
       grind)
    | exact resolve eq1263634 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291 eq1263634
  have eq1263941 : ∀ X0 : G, (σ (M.op x y)) ≠ (k X0 (σ y)) ∨ (σ (M.op x y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq1061617 eq1263877
    | (have j0 := eq1263877 X0
       grind)
    | exact resolve eq1263877 eq1061617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263877
  have eq1264230 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k X0 y)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq40 eq1263941
    | (have j0 := eq1263941 (σ X0)
       grind)
    | exact resolve eq1263941 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1263941
  have eq1646414 : (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq131289 eq49353
    | exact resolve eq49353 eq131289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49353 eq131289
  have eq1647795 : (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq1646414
  have eq1648065 : (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) = (k (M.op (σ x) (σ (M.op x y))) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1061617 eq1647795
    | exact resolve eq1647795 eq1061617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647795
  have eq1648616 : (σ (M.op x y)) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1066045 eq1648065
    | exact resolve eq1648065 eq1066045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066045 eq1648065
  have eq1648997 : (σ (M.op x y)) = (M.op (M.op x y) (M.op x (k (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1648616
       have i₂ := eq54 (k sF2 sF3)
       grind)
    | exact superpose eq54 eq1648616
    | exact resolve eq1648616 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1648616
  have eq1649133 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op x y) (M.op x (k (σ x) (σ y)))) := by
    first
    | exact superpose eq1061617 eq1648997
    | exact resolve eq1648997 eq1061617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061617 eq1648997
  have eq1649218 : (σ (M.op x y)) = (M.op (M.op x y) (M.op x (k (σ x) (σ y)))) := by
    first
    | (have r₁ := eq1649133
       have r₂ := eq27
       grind)
    | exact resolve eq1649133 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649133
  have eq1741275 : (M.op (M.op x y) (M.op x (k (σ x) (σ y)))) = (σ (M.op (M.op x y) (M.op x (M.op x x)))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq674
       have i₂ := eq1061388
       grind)
    | exact superpose eq1061388 eq674
    | exact resolve eq674 eq1061388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq1741283 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1264230 x
       have i₂ := eq1061388
       grind)
    | exact superpose eq1061388 eq1264230
    | (have j0 := eq1264230 x
       grind)
    | exact resolve eq1264230 eq1061388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061388 eq1264230
  have eq1741335 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1741283
       have i₂ := eq140
       grind)
    | exact superpose eq140 eq1741283
    | exact resolve eq1741283 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1741283
  have eq1741343 : (σ (M.op x x)) = (M.op (M.op x y) (M.op x (k (σ x) (σ y)))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq266 eq1741275
    | exact resolve eq1741275 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq1741275
  have eq1741371 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1741335
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1741335
    | exact resolve eq1741335 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1741335
  have eq1741373 : (σ (M.op x y)) = (σ (M.op x x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1649218 eq1741343
    | exact resolve eq1741343 eq1649218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649218 eq1741343
  have eq1741393 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq1741371
    | exact resolve eq1741371 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1741371
  have eq1741395 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1741373
       have i₂ := eq140
       grind)
    | exact superpose eq140 eq1741373
    | exact resolve eq1741373 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq1741373
  have eq1741413 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq1741393
       have r₂ := eq27
       grind)
    | exact resolve eq1741393 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1741393
  have eq1742404 : y = (M.op y x) := by
    first
    | (have r₁ := eq1741413
       have r₂ := eq1741395
       grind)
    | exact resolve eq1741413 eq1741395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1741395 eq1741413
  have eq1742430 : y ≠ y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1742404
       grind)
    | exact superpose eq1742404 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1742404
       grind)
    | exact resolve eq13 eq1742404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1742404
  have eq1742671 : (M.op x y) = (k x y) := by grind
  clear eq1742430
  have eq1742779 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1742671
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1742671
    | exact resolve eq1742671 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1742671
  have eq1743414 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1742779
       grind)
    | exact superpose eq1742779 eq44
    | exact resolve eq44 eq1742779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1742779
  have eq1743501 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1743414
    | exact resolve eq1743414 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1743414
  have eq1743532 : False := by grind
  exact eq1743532
